//! A pointer type for heap allocation.
//!
//! [`Box<T, B>`], casually referred to as a 'box', provides the simplest form of allocation in
//! Rust. Boxes provide ownership for this allocation, and drop their contents when they go out of
//! scope.
//!
//! # Examples
//!
//! Move a value from the stack to the heap by creating a [`Box`]:
//!
//! ```
//! use alloc_wg::boxed::Box;
//!
//! let val: u8 = 5;
//! # #[allow(unused_variables)]
//! let boxed: Box<u8> = Box::new(val);
//! ```
//!
//! Move a value from a [`Box`] back to the stack by [dereferencing]:
//!
//! ```
//! use alloc_wg::boxed::Box;
//!
//! let boxed: Box<u8> = Box::new(5);
//! # #[allow(unused_variables)]
//! let val: u8 = *boxed;
//! ```
//!
//! Creating a recursive data structure:
//!
//! ```
//! use alloc_wg::boxed::Box;
//!
//! #[derive(Debug)]
//! enum List<T> {
//!     Cons(T, Box<List<T>>),
//!     Nil,
//! }
//!
//! fn main() {
//!     let list: List<i32> = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
//!     println!("{:?}", list);
//! }
//! ```
//!
//! This will print `Cons(1, Cons(2, Nil))`.
//!
//! Recursive structures must be boxed, because if the definition of `Cons`
//! looked like this:
//!
//! ```compile_fail,E0072
//! # enum List<T> {
//! Cons(T, List<T>),
//! # }
//! ```
//!
//! It wouldn't work. This is because the size of a `List` depends on how many elements are in the
//! list, and so we don't know how much memory to allocate for a `Cons`. By introducing a [`Box<T,
//! D>`], which has a defined size, we know how big `Cons` needs to be.
//!
//! # Memory layout
//!
//! For non-zero-sized values, a [`Box`] will use the [`Global`] allocator for its allocation if no
//! allocator was specified. It is valid to convert both ways between a [`Box`] and a raw pointer
//! allocated with the same allocator, given that the [`Layout`] used with the allocator is
//! correct for the type. More precisely, a `value: *mut T` that has been allocated with the
//! [`Global`] allocator with `Layout::for_value(&*value)` may be converted into a box using
//! [`Box::<T>::from_raw(value)`]. For other allocators, [`Box::<T>::from_raw_in(value, alloc)`] may
//! be used. Conversely, the memory backing a `value: *mut T` obtained from [`Box::<T>::into_raw`]
//! may be deallocated using the specific allocator with [`Layout::for_value(&*value)`].
//!
//!
//! [dereferencing]: core::ops::Deref
//! [`Box`]: crate::boxed::Box
//! [`Box<T>`]: crate::boxed::Box
//! [`Box::<T>::from_raw(value)`]: crate::boxed::Box::from_raw
//! [`Box::<T>::from_raw(value, alloc)`]: crate::boxed::Box::from_raw_in
//! [`Box::<T>::into_raw`]: crate::boxed::Box::into_raw
//! [`Global`]: crate::alloc::Global
//! [`Layout`]: crate::alloc::Layout
//! [`Layout::for_value(&*value)`]: crate::alloc::Layout::for_value

use crate::{
    alloc::{AbortAlloc, AllocRef, BuildAlloc, DeallocRef, Global, NonZeroLayout},
    collections::CollectionAllocErr,
    UncheckedResultExt,
};
#[cfg(feature = "ptr_internals")]
use core::ptr::Unique;
use core::{
    fmt,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::{self, NonNull},
    slice,
};

/// A pointer type for heap allocation.
///
/// See the [module-level documentation](index.html) for more.
// Using `NonNull` + `PhantomData` instead of `Unique` to stay on stable as long as possible
pub struct Box<T: ?Sized, B: BuildAlloc = AbortAlloc<Global>>(NonNull<T>, B, PhantomData<T>);

#[allow(clippy::use_self)]
impl<T> Box<T> {
    /// Allocates memory on the heap and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// # #[allow(unused_variables)]
    /// let five = Box::new(5);
    /// ```
    pub fn new(x: T) -> Self {
        Self::new_in(x, AbortAlloc(Global))
    }

    /// Constructs a new box with uninitialized contents.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let mut five = Box::<u32>::new_uninit();
    ///
    /// let five = unsafe {
    ///     // Deferred initialization:
    ///     five.as_mut_ptr().write(5);
    ///
    ///     five.assume_init()
    /// };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    pub fn new_uninit() -> Box<mem::MaybeUninit<T>> {
        Self::new_uninit_in(AbortAlloc(Global))
    }

    /// Constructs a new `Pin<Box<T>>`. If `T` does not implement `Unpin`, then
    /// `x` will be pinned in memory and unable to be moved.
    #[inline(always)]
    pub fn pin(x: T) -> Pin<Self> {
        Self::new(x).into()
    }
}

#[allow(clippy::use_self)]
impl<T, B: BuildAlloc> Box<T, B>
where
    B::Ref: AllocRef,
{
    /// Allocates memory with the given allocator and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{
    ///     alloc::{AbortAlloc, Global},
    ///     boxed::Box,
    /// };
    ///
    /// # #[allow(unused_variables)]
    /// let five: Box<_, AbortAlloc<Global>> = Box::new_in(5, AbortAlloc(Global));
    /// ```
    pub fn new_in(x: T, a: B::Ref) -> Self
    where
        B::Ref: AllocRef<Error = crate::Never>,
    {
        unsafe { Self::try_new_in(x, a).unwrap_unchecked() }
    }

    /// Tries to allocate memory with the given allocator and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// # #[allow(unused_variables)]
    /// let five: Box<_, Global> = Box::try_new_in(5, Global)?;
    /// # Ok::<_, alloc_wg::alloc::AllocErr>(())
    /// ```
    pub fn try_new_in(x: T, mut a: B::Ref) -> Result<Self, <B::Ref as AllocRef>::Error> {
        let ptr = if let Ok(layout) = NonZeroLayout::new::<T>() {
            let ptr = a.alloc(layout)?.cast::<T>();
            unsafe {
                ptr.as_ptr().write(x);
            }
            ptr
        } else {
            NonNull::dangling()
        };
        Ok(Self(ptr, a.get_build_alloc(), PhantomData))
    }

    /// Constructs a new box with uninitialized contents in a specified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{
    ///     alloc::{AbortAlloc, Global},
    ///     boxed::Box,
    /// };
    ///
    /// let mut five = Box::<u32, AbortAlloc<Global>>::new_uninit_in(AbortAlloc(Global));
    ///
    /// let five = unsafe {
    ///     // Deferred initialization:
    ///     five.as_mut_ptr().write(5);
    ///
    ///     five.assume_init()
    /// };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    pub fn new_uninit_in(a: B::Ref) -> Box<mem::MaybeUninit<T>, B>
    where
        B::Ref: AllocRef<Error = crate::Never>,
    {
        unsafe { Self::try_new_uninit_in(a).unwrap_unchecked() }
    }

    /// Tries to construct a new box with uninitialized contents in a specified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// let mut five = Box::<u32, Global>::try_new_uninit_in(Global)?;
    ///
    /// let five = unsafe {
    ///     // Deferred initialization:
    ///     five.as_mut_ptr().write(5);
    ///
    ///     five.assume_init()
    /// };
    ///
    /// assert_eq!(*five, 5);
    /// # Ok::<_, alloc_wg::alloc::AllocErr>(())
    /// ```
    pub fn try_new_uninit_in(
        mut a: B::Ref,
    ) -> Result<Box<mem::MaybeUninit<T>, B>, <B::Ref as AllocRef>::Error> {
        let ptr = if let Ok(layout) = NonZeroLayout::new::<T>() {
            let ptr: NonNull<T> = a.alloc(layout)?.cast();
            ptr
        } else {
            NonNull::dangling()
        };
        Ok(Self(ptr.cast(), a.get_build_alloc(), PhantomData))
    }

    /// Constructs a new `Pin<Box<T, A>>` with the specified allocator. If `T` does not implement
    /// `Unpin`, then `x` will be pinned in memory and unable to be moved.
    #[inline(always)]
    pub fn pin_in(x: T, a: B::Ref) -> Pin<Self>
    where
        B::Ref: AllocRef<Error = crate::Never>,
    {
        unsafe { Self::try_pin_in(x, a).unwrap_unchecked() }
    }

    /// Constructs a new `Pin<Box<T, A>>` with the specified allocator. If `T` does not implement
    /// `Unpin`, then `x` will be pinned in memory and unable to be moved.
    #[inline(always)]
    pub fn try_pin_in(x: T, a: B::Ref) -> Result<Pin<Self>, <B::Ref as AllocRef>::Error> {
        Self::try_new_in(x, a).map(Pin::from)
    }
}

#[allow(clippy::use_self)]
impl<T> Box<[T]> {
    /// Construct a new boxed slice with uninitialized contents.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let mut values = Box::<[u32]>::new_uninit_slice(3);
    ///
    /// let values = unsafe {
    ///     // Deferred initialization:
    ///     values[0].as_mut_ptr().write(1);
    ///     values[1].as_mut_ptr().write(2);
    ///     values[2].as_mut_ptr().write(3);
    ///
    ///     values.assume_init()
    /// };
    ///
    /// assert_eq!(*values, [1, 2, 3]);
    /// ```
    pub fn new_uninit_slice(len: usize) -> Box<[mem::MaybeUninit<T>]> {
        Self::new_uninit_slice_in(len, AbortAlloc(Global))
    }
}

#[allow(clippy::use_self)]
impl<T, B: BuildAlloc> Box<[T], B>
where
    B::Ref: AllocRef,
{
    /// Construct a new boxed slice with uninitialized contents with the spoecified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{
    ///     alloc::{AbortAlloc, Global},
    ///     boxed::Box,
    /// };
    ///
    /// let mut values = Box::<[u32], AbortAlloc<Global>>::new_uninit_slice_in(3, AbortAlloc(Global));
    ///
    /// let values = unsafe {
    ///     // Deferred initialization:
    ///     values[0].as_mut_ptr().write(1);
    ///     values[1].as_mut_ptr().write(2);
    ///     values[2].as_mut_ptr().write(3);
    ///
    ///     values.assume_init()
    /// };
    ///
    /// assert_eq!(*values, [1, 2, 3]);
    /// ```
    pub fn new_uninit_slice_in(len: usize, a: B::Ref) -> Box<[mem::MaybeUninit<T>], B>
    where
        B::Ref: AllocRef<Error = crate::Never>,
    {
        unsafe { Self::try_new_uninit_slice_in(len, a).unwrap_unchecked() }
    }

    /// Tries to construct a new boxed slice with uninitialized contents with the spoecified
    /// allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// let mut values = Box::<[u32], Global>::try_new_uninit_slice_in(3, Global)?;
    ///
    /// let values = unsafe {
    ///     // Deferred initialization:
    ///     values[0].as_mut_ptr().write(1);
    ///     values[1].as_mut_ptr().write(2);
    ///     values[2].as_mut_ptr().write(3);
    ///
    ///     values.assume_init()
    /// };
    ///
    /// assert_eq!(*values, [1, 2, 3]);
    /// # Ok::<_, alloc_wg::collections::CollectionAllocErr<Global>>(())
    /// ```
    pub fn try_new_uninit_slice_in(
        len: usize,
        mut a: B::Ref,
    ) -> Result<Box<[mem::MaybeUninit<T>], B>, CollectionAllocErr<B>> {
        let ptr = if mem::size_of::<T>() == 0 || len == 0 {
            NonNull::dangling()
        } else {
            let layout = NonZeroLayout::array::<mem::MaybeUninit<T>>(len)?;
            a.alloc(layout)
                .map_err(|inner| CollectionAllocErr::AllocError { layout, inner })?
        };
        unsafe {
            let slice = slice::from_raw_parts_mut(ptr.cast().as_ptr(), len);
            Ok(Self(NonNull::from(slice), a.get_build_alloc(), PhantomData))
        }
    }
}

#[allow(clippy::use_self)]
impl<T, B: BuildAlloc> Box<mem::MaybeUninit<T>, B> {
    /// Converts to `Box<T, B>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let mut five = Box::<u32>::new_uninit();
    ///
    /// let five = unsafe {
    ///     // Deferred initialization:
    ///     five.as_mut_ptr().write(5);
    ///
    ///     five.assume_init()
    /// };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[inline]
    pub unsafe fn assume_init(self) -> Box<T, B> {
        let (ptr, b) = Self::into_raw_alloc(self);
        Box::from_raw_in(ptr as _, b)
    }
}

#[allow(clippy::use_self)]
impl<T, B: BuildAlloc> Box<[mem::MaybeUninit<T>], B> {
    /// Converts to `Box<[T], B>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the values
    /// really are in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: core::mem::MaybeUninit::assume_init
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let mut values = Box::<[u32]>::new_uninit_slice(3);
    ///
    /// let values = unsafe {
    ///     // Deferred initialization:
    ///     values[0].as_mut_ptr().write(1);
    ///     values[1].as_mut_ptr().write(2);
    ///     values[2].as_mut_ptr().write(3);
    ///
    ///     values.assume_init()
    /// };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[inline]
    pub unsafe fn assume_init(self) -> Box<[T], B> {
        let (ptr, b) = Self::into_raw_alloc(self);
        Box::from_raw_in(ptr as _, b)
    }
}

impl<T: ?Sized> Box<T> {
    /// Constructs a box from a raw pointer.
    ///
    /// After calling this function, the raw pointer is owned by the resulting `Box`.2 Specifically,
    /// the `Box` destructor will call the destructor of `T` and free the allocated memory. For
    /// this to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to memory problems. For example, a
    /// double-free may occur if the function is called twice on the same raw pointer.
    ///
    /// # Examples
    ///
    /// Recreate a `Box` which was previously converted to a raw pointer using [`Box::into_raw`][]:
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(5);
    /// let ptr = Box::into_raw(x);
    /// # #[allow(unused_variables)]
    /// let x = unsafe { Box::from_raw(ptr) };
    /// ```
    /// Manually create a `Box` from scratch by using the global allocator:
    /// ```
    /// use alloc_wg::{
    ///     alloc::{alloc, Layout},
    ///     boxed::Box,
    /// };
    ///
    /// unsafe {
    ///     let ptr = alloc(Layout::new::<i32>()) as *mut i32;
    ///     *ptr = 5;
    /// # #[allow(unused_variables)]
    ///     let x = Box::from_raw(ptr);
    /// }
    /// ```
    ///
    /// [memory layout]: index.html#memory-layout
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        Self::from_raw_in(raw, AbortAlloc(Global))
    }
}

impl<T: ?Sized, B: BuildAlloc> Box<T, B> {
    /// Constructs a box from a raw pointer.
    ///
    /// After calling this function, the raw pointer is owned by the resulting `Box`. Specifically,
    /// the `Box` destructor will call the destructor of `T` and free the allocated memory. For
    /// this to be safe, the memory must have been allocated in accordance
    /// with the [memory layout] used by `Box` .
    ///
    /// # Safety
    ///
    /// This function is unsafe because improper use may lead to memory problems. For example, a
    /// double-free may occur if the function is called twice on the same raw pointer.
    ///
    /// # Example
    ///
    /// Manually create a `Box` from scratch by using the global allocator:
    /// ```
    /// use alloc_wg::{
    ///     alloc::{alloc, Global, Layout},
    ///     boxed::Box,
    /// };
    ///
    /// unsafe {
    ///     let ptr = alloc(Layout::new::<i32>()) as *mut i32;
    ///     *ptr = 5;
    /// #    #[allow(unused_variables)]
    ///     let x: Box<_, Global> = Box::from_raw_in(ptr, Global);
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw_in(raw: *mut T, d: B) -> Self {
        Self(NonNull::new_unchecked(raw), d, PhantomData)
    }

    pub fn alloc_builder(&self) -> &B {
        &self.1
    }

    pub fn alloc_builder_mut(&mut self) -> &mut B {
        &mut self.1
    }

    pub fn alloc_ref(&mut self) -> B::Ref {
        unsafe {
            self.1
                .build_alloc_ref(self.0.cast(), NonZeroLayout::for_value(self.as_ref()))
        }
    }
    /// Consumes the `Box`, returning a wrapped raw pointer.
    ///
    /// The pointer will be properly aligned and non-null.
    ///
    /// After calling this function, the caller is responsible for the memory previously managed by
    /// the `Box`. In particular, the caller should properly destroy `T` and release the memory,
    /// taking into account the [memory layout] used by `Box`. The easiest way to do this is to
    /// convert the raw pointer back into a `Box` with the [`Box::from_raw`][] function,
    /// allowing the `Box` destructor to perform the cleanup.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `Box::into_raw(b)` instead of `b.into_raw()`. This is so that there is no conflict with
    /// a method on the inner type.
    ///
    /// # Examples
    /// Converting the raw pointer back into a `Box` with [`Box::from_raw`][] for automatic cleanup:
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let ptr = Box::into_raw(x);
    /// # #[allow(unused_variables)]
    /// let x = unsafe { Box::from_raw(ptr) };
    /// ```
    /// Manual cleanup by explicitly running the destructor and deallocating
    /// the memory:
    /// ```
    /// use alloc_wg::{
    ///     alloc::{dealloc, Layout},
    ///     boxed::Box,
    /// };
    /// use core::ptr;
    ///
    /// let x = Box::new(String::from("Hello"));
    /// let p = Box::into_raw(x);
    /// unsafe {
    ///     ptr::drop_in_place(p);
    ///     dealloc(p as *mut u8, Layout::new::<String>());
    /// }
    /// ```
    ///
    /// [memory layout]: index.html#memory-layout
    #[inline]
    pub fn into_raw(b: Self) -> *mut T {
        Self::into_raw_alloc(b).0
    }

    #[inline]
    pub fn into_raw_alloc(b: Self) -> (*mut T, B) {
        let (p, b) = Self::into_raw_non_null_alloc(b);
        (p.as_ptr(), b)
    }

    /// Consumes the `Box`, returning the wrapped pointer as `NonNull<T>`.
    ///
    /// After calling this function, the caller is responsible for the memory previously managed by
    /// the `Box`. In particular, the caller should properly destroy `T` and release the memory.
    /// The easiest way to do so is to convert the `NonNull<T>` pointer
    /// into a raw pointer and back into a `Box` with the [`Box::from_raw`][]
    /// function.
    ///
    /// Note: this is an associated function, which means that you have to call it as
    /// `Box::into_raw_non_null(b)` instead of `b.into_raw_non_null()`. This is so that there is no
    /// conflict with a method on the inner type.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(5);
    /// let ptr = Box::into_raw_non_null(x);
    ///
    /// // Clean up the memory by converting the NonNull pointer back
    /// // into a Box and letting the Box be dropped.
    /// # #[allow(unused_variables)]
    /// let x = unsafe { Box::from_raw(ptr.as_ptr()) };
    /// ```
    #[inline]
    pub fn into_raw_non_null(b: Self) -> NonNull<T> {
        Self::into_raw_non_null_alloc(b).0
    }

    #[inline]
    pub fn into_raw_non_null_alloc(b: Self) -> (NonNull<T>, B) {
        // TODO: Replace with `Self::into_unique_alloc(b).into()`
        let mut ptr = b.0;
        unsafe {
            let alloc = ptr::read(&b.1);
            mem::forget(b);
            (NonNull::new_unchecked(ptr.as_mut()), alloc)
        }
    }

    #[inline]
    #[doc(hidden)]
    #[cfg(feature = "ptr_internals")]
    pub fn into_unique(b: Self) -> Unique<T> {
        Self::into_unique_alloc(b).0
    }

    #[inline]
    #[doc(hidden)]
    #[cfg(feature = "ptr_internals")]
    pub fn into_unique_alloc(b: Self) -> (Unique<T>, B) {
        let mut ptr = b.0;
        unsafe {
            let alloc = ptr::read(&b.1);
            mem::forget(b);

            // Box is kind-of a library type, but recognized as a "unique pointer" by
            // Stacked Borrows.  This function here corresponds to "reborrowing to
            // a raw pointer", but there is no actual reborrow here -- so
            // without some care, the pointer we are returning here still carries
            // the tag of `b`, with `Unique` permission.
            // We round-trip through a mutable reference to avoid that.
            (Unique::new_unchecked(ptr.as_mut()), alloc)
        }
    }

    /// Consumes and leaks the `Box`, returning a mutable reference,
    /// `&'a mut T`. Note that the type `T` must outlive the chosen lifetime
    /// `'a`. If the type has only static references, or none at all, then this
    /// may be chosen to be `'static`.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak. If this is not acceptable, the reference should first be wrapped
    /// with the [`Box::from_raw`][] function producing a `Box`. This `Box` can
    /// then be dropped which will properly destroy `T` and release the
    /// allocated memory.
    ///
    /// Note: this is an associated function, which means that you have
    /// to call it as `Box::leak(b)` instead of `b.leak()`. This
    /// is so that there is no conflict with a method on the inner type.
    ///
    /// # Examples
    ///
    /// Simple usage:
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(41);
    /// let static_ref: &'static mut usize = Box::leak(x);
    /// *static_ref += 1;
    /// assert_eq!(*static_ref, 42);
    /// ```
    // TODO: Example for unsized data
    #[inline]
    pub fn leak<'a>(b: Self) -> &'a mut T
    where
        T: 'a, // Technically not needed, but kept to be explicit.
    {
        unsafe { &mut *Self::into_raw(b) }
    }

    /// Converts a `Box<T, B>` into a `Pin<Box<T, B>>`
    ///
    /// This conversion does not allocate and happens in place.
    ///
    /// This is also available via [`From`][].
    pub fn into_pin(boxed: Self) -> Pin<Self> {
        // It's not possible to move or replace the insides of a `Pin<Box<T>>`
        // when `T: !Unpin`,  so it's safe to pin it directly without any
        // additional requirements.
        unsafe { Pin::new_unchecked(boxed) }
    }
}

impl<T: ?Sized, B: BuildAlloc> Deref for Box<T, B> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }
}
impl<T: ?Sized, B: BuildAlloc> DerefMut for Box<T, B> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut() }
    }
}

impl<T: ?Sized, B: BuildAlloc> From<Box<T, B>> for Pin<Box<T, B>> {
    /// Converts a `Box<T, B>` into a `Pin<Box<T, B>>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    fn from(boxed: Box<T, B>) -> Self {
        Box::into_pin(boxed)
    }
}

impl<T: fmt::Display + ?Sized, B: BuildAlloc> fmt::Display for Box<T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}
impl<T: fmt::Debug + ?Sized, B: BuildAlloc> fmt::Debug for Box<T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, B: BuildAlloc> AsRef<T> for Box<T, B> {
    fn as_ref(&self) -> &T {
        &**self
    }
}
impl<T: ?Sized, B: BuildAlloc> AsMut<T> for Box<T, B> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

#[cfg(feature = "dropck_eyepatch")]
unsafe impl<#[may_dangle] T: ?Sized, B: BuildAlloc> Drop for Box<T, B> {
    fn drop(&mut self) {
        unsafe {
            self.alloc_ref().dealloc(
                self.0.cast(),
                NonZeroLayout::for_value_unchecked(self.0.as_ref()),
            )
        }
    }
}

#[cfg(not(feature = "dropck_eyepatch"))]
impl<T: ?Sized, B: BuildAlloc> Drop for Box<T, B> {
    fn drop(&mut self) {
        unsafe {
            self.alloc_ref().dealloc(
                self.0.cast(),
                NonZeroLayout::for_value_unchecked(self.0.as_ref()),
            )
        }
    }
}
