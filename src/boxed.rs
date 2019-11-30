//! A pointer type for heap allocation.
//!
//! [`Box<T, A>`], casually referred to as a 'box', provides the simplest form of allocation in
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
//! let list: List<i32> = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
//! println!("{:?}", list);
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
//! allocated with the same allocator, given that the [`NonZeroLayout`] used with the allocator is
//! correct for the type. More precisely, a `value: *mut T` that has been allocated with the
//! [`Global`] allocator with `Layout::for_value(&*value)` may be converted into a box using
//! [`Box::<T>::from_raw(value)`]. For other allocators, [`Box::<T>::from_raw_in(value, alloc)`] may
//! be used. Conversely, the memory backing a `value: *mut T` obtained from [`Box::<T>::into_raw`]
//! may be deallocated using the specific allocator with [`NonZeroLayout::for_value(&*value)`].
//!
//!
//! [dereferencing]: core::ops::Deref
//! [`Box`]: crate::boxed::Box
//! [`Box<T, A>`]: crate::boxed::Box
//! [`Box::<T>::from_raw(value)`]: crate::boxed::Box::from_raw
//! [`Box::<T>::from_raw(value, alloc)`]: crate::boxed::Box::from_raw_in
//! [`Box::<T>::into_raw`]: crate::boxed::Box::into_raw
//! [`Global`]: crate::alloc::Global
//! [`NonZeroLayout`]: crate::alloc::NonZeroLayout
//! [`NonZeroLayout::for_value(&*value)`]: crate::alloc::NonZeroLayout::for_value

use crate::{
    alloc::{AllocRef, BuildAllocRef, DeallocRef, Global, NonZeroLayout, AbortAlloc},
    clone::CloneIn,
    collections::CollectionAllocErr,
    raw_vec::RawVec,
};
use core::{
    any::Any,
    borrow,
    cmp::Ordering,
    fmt,
    future::Future,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    mem,
    num::NonZeroUsize,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::{self, NonNull, Unique},
    slice,
    task::{Context, Poll},
};

/// A pointer type for heap allocation.
///
/// See the [module-level documentation](index.html) for more.
pub struct Box<T: ?Sized, A: DeallocRef = AbortAlloc<Global>> {
    ptr: Unique<T>,
    build_alloc: A::BuildAlloc,
}
// TODO: Remove when using ptr::Unique
unsafe impl<T: ?Sized, A: DeallocRef + Send> Send for Box<T, A> {}
unsafe impl<T: ?Sized, A: DeallocRef + Sync> Sync for Box<T, A> {}

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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    #[must_use]
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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    #[must_use]
    pub fn new_uninit() -> Box<mem::MaybeUninit<T>> {
        Self::new_uninit_in(AbortAlloc(Global))
    }

    /// Constructs a new `Pin<Box<T>>`. If `T` does not implement `Unpin`, then
    /// `x` will be pinned in memory and unable to be moved.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn pin(x: T) -> Pin<Self> {
        Self::new(x).into()
    }
}

#[allow(clippy::use_self)]
impl<T, A: AllocRef> Box<T, A> {
    /// Allocates memory with the given allocator and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// # #[allow(unused_variables)]
    /// let five = Box::new_in(5, Global);
    /// ```
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn new_in(x: T, a: A) -> Self
    where
        A: AllocRef<Error = !>,
    {
        let Ok(b) = Self::try_new_in(x, a);
        b
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
    /// let five = Box::try_new_in(5, Global)?;
    /// # Ok::<_, alloc_wg::alloc::AllocErr>(())
    /// ```
    pub fn try_new_in(x: T, mut a: A) -> Result<Self, A::Error> {
        let ptr = if let Ok(layout) = NonZeroLayout::new::<T>() {
            let ptr = a.alloc(layout)?.cast::<T>();
            unsafe {
                ptr.as_ptr().write(x);
            }
            ptr
        } else {
            NonNull::dangling()
        };
        unsafe { Ok(Self::from_raw_in(ptr.as_ptr(), a.get_build_alloc())) }
    }

    /// Constructs a new box with uninitialized contents in a specified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// let mut five = Box::<u32, _>::new_uninit_in(Global);
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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn new_uninit_in(a: A) -> Box<mem::MaybeUninit<T>, A>
    where
        A: AllocRef<Error = !>,
    {
        let Ok(b) = Self::try_new_uninit_in(a);
        b
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
    pub fn try_new_uninit_in(mut a: A) -> Result<Box<mem::MaybeUninit<T>, A>, A::Error> {
        let ptr = if let Ok(layout) = NonZeroLayout::new::<T>() {
            let ptr: NonNull<mem::MaybeUninit<T>> = a.alloc(layout)?.cast();
            ptr
        } else {
            NonNull::dangling()
        };
        unsafe { Ok(Box::from_raw_in(ptr.as_ptr(), a.get_build_alloc())) }
    }

    /// Constructs a new `Pin<Box<T, A>>` with the specified allocator. If `T` does not implement
    /// `Unpin`, then `x` will be pinned in memory and unable to be moved.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn pin_in(x: T, a: A) -> Pin<Self>
    where
        A: AllocRef<Error = !>,
    {
        let Ok(b) = Self::try_pin_in(x, a);
        b
    }

    /// Constructs a new `Pin<Box<T, A>>` with the specified allocator. If `T` does not implement
    /// `Unpin`, then `x` will be pinned in memory and unable to be moved.
    #[inline]
    pub fn try_pin_in(x: T, a: A) -> Result<Pin<Self>, A::Error> {
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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    #[must_use]
    pub fn new_uninit_slice(len: usize) -> Box<[mem::MaybeUninit<T>]> {
        Self::new_uninit_slice_in(len, AbortAlloc(Global))
    }
}

#[allow(clippy::use_self)]
impl<T, A: AllocRef<Error = !>> Box<[T], A> {
    /// Construct a new boxed slice with uninitialized contents with the spoecified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// let mut values = Box::<[u32], _>::new_uninit_slice_in(3, Global);
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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn new_uninit_slice_in(len: usize, a: A) -> Box<[mem::MaybeUninit<T>], A> {
        match Self::try_new_uninit_slice_in(len, a) {
            Ok(b) => b,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            #[allow(unreachable_patterns)] // TODO rustc bug?
            Err(CollectionAllocErr::AllocError { inner: e, .. }) => e,
        }
    }
}

#[allow(clippy::use_self)]
impl<T, A: AllocRef> Box<[T], A> {
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
        mut a: A,
    ) -> Result<Box<[mem::MaybeUninit<T>], A>, CollectionAllocErr<A>> {
        let ptr = if mem::size_of::<T>() == 0 || len == 0 {
            NonNull::dangling()
        } else {
            let len = unsafe { NonZeroUsize::new_unchecked(len) };
            let layout = NonZeroLayout::array::<mem::MaybeUninit<T>>(len)?;
            a.alloc(layout)
                .map_err(|inner| CollectionAllocErr::AllocError { layout, inner })?
                .cast()
        };
        unsafe {
            let slice = slice::from_raw_parts_mut(ptr.as_ptr(), len);
            Ok(Box::from_raw_in(
                NonNull::from(slice).as_ptr(),
                a.get_build_alloc(),
            ))
        }
    }
}

#[allow(clippy::use_self)]
impl<T, A: DeallocRef> Box<mem::MaybeUninit<T>, A> {
    /// Converts to `Box<T, A>`.
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
    pub unsafe fn assume_init(self) -> Box<T, A> {
        let (ptr, b) = Self::into_raw_alloc(self);
        Box::from_raw_in((*ptr).as_mut_ptr(), b)
    }
}

#[allow(clippy::use_self)]
impl<T, A: DeallocRef> Box<[mem::MaybeUninit<T>], A> {
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
    pub unsafe fn assume_init(self) -> Box<[T], A> {
        let (ptr, b) = Self::into_raw_alloc(self);
        Box::from_raw_in(ptr as *mut [T], b)
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
    /// use alloc_wg::{alloc::alloc, boxed::Box};
    /// use core::alloc::Layout;
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
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        Self::from_raw_in(raw, AbortAlloc(Global))
    }
}

impl<T: ?Sized, A: DeallocRef> Box<T, A> {
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
    ///     alloc::{alloc, Global},
    ///     boxed::Box,
    /// };
    /// use core::alloc::Layout;
    ///
    /// unsafe {
    ///     let ptr = alloc(Layout::new::<i32>()) as *mut i32;
    ///     *ptr = 5;
    /// #    #[allow(unused_variables)]
    ///     let x: Box<_, Global> = Box::from_raw_in(ptr, Global);
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw_in(raw: *mut T, builder: A::BuildAlloc) -> Self {
        Self {
            ptr: Unique::new_unchecked(raw),
            build_alloc: builder,
        }
    }

    /// Returns a shared reference to the associated `BuildAlloc`
    pub fn build_alloc(&self) -> &A::BuildAlloc {
        &self.build_alloc
    }

    /// Returns a mutable reference to the associated `BuildAlloc`
    pub fn build_alloc_mut(&mut self) -> &mut A::BuildAlloc {
        &mut self.build_alloc
    }

    /// Returns the allocator and it's currently used layout. If `T` is a ZST, no layout is returned.
    pub fn alloc_ref(&mut self) -> (A, Option<NonZeroLayout>) {
        let layout = NonZeroLayout::for_value(self.as_ref());
        let ptr = self.ptr.cast();
        let alloc = unsafe { self.build_alloc_mut().build_alloc_ref(ptr.into(), layout) };
        (alloc, layout)
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
    /// use alloc_wg::{alloc::dealloc, boxed::Box};
    /// use core::{alloc::Layout, ptr};
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
    pub fn into_raw_alloc(b: Self) -> (*mut T, A::BuildAlloc) {
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
    pub fn into_raw_non_null_alloc(b: Self) -> (NonNull<T>, A::BuildAlloc) {
        // TODO: Replace with `Self::into_unique_alloc(b).into()`
        let mut ptr = b.ptr;
        unsafe {
            let alloc = ptr::read(b.build_alloc());
            mem::forget(b);
            (NonNull::new_unchecked(ptr.as_mut()), alloc)
        }
    }

    #[inline]
    #[doc(hidden)]
    pub fn into_unique(b: Self) -> Unique<T> {
        Self::into_unique_alloc(b).0
    }

    #[inline]
    #[doc(hidden)]
    pub fn into_unique_alloc(b: Self) -> (Unique<T>, A::BuildAlloc) {
        let ptr = b.ptr;
        unsafe {
            let alloc = ptr::read(b.build_alloc());
            mem::forget(b);

            // Box is kind-of a library type, but recognized as a "unique pointer" by
            // Stacked Borrows.  This function here corresponds to "reborrowing to
            // a raw pointer", but there is no actual reborrow here -- so
            // without some care, the pointer we are returning here still carries
            // the tag of `b`, with `Unique` permission.
            // We round-trip through a mutable reference to avoid that.
            (ptr, alloc)
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

    /// Converts a `Box<T, A>` into a `Pin<Box<T, A>>`
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

fn drop_box<T: ?Sized, A: DeallocRef>(boxed: &mut Box<T, A>) {
    unsafe {
        let ptr = boxed.ptr;
        ptr::drop_in_place(ptr.as_ptr());
        if let (mut alloc, Some(layout)) = boxed.alloc_ref() {
            alloc.dealloc(ptr.cast().into(), layout)
        }
    }
}

unsafe impl<#[may_dangle] T: ?Sized, A: DeallocRef> Drop for Box<T, A> {
    fn drop(&mut self) {
        drop_box(self);
    }
}

impl<T, A> Default for Box<T, A>
where
    T: Default,
    A: Default + AllocRef<Error = !>,
{
    #[must_use]
    fn default() -> Self {
        Self::new_in(T::default(), A::default())
    }
}

#[allow(clippy::use_self)]
impl<T, A: AllocRef<Error = !>> Default for Box<[T], A>
where
    A: Default + AllocRef,
{
    #[must_use]
    fn default() -> Self {
        Box::<[T; 0], A>::new_in([], A::default())
    }
}

#[inline]
unsafe fn from_boxed_utf8_unchecked<A: DeallocRef>(v: Box<[u8], A>) -> Box<str, A> {
    let (ptr, b) = Box::into_raw_alloc(v);
    Box::from_raw_in(ptr as *mut str, b)
}

#[allow(clippy::use_self)]
impl<A: AllocRef<Error = !>> Default for Box<str, A>
where
    A: Default + AllocRef,
{
    #[must_use]
    fn default() -> Self {
        unsafe { from_boxed_utf8_unchecked(Box::default()) }
    }
}

impl<T: Clone, A: AllocRef<Error = !>> Clone for Box<T, A>
where
    A: AllocRef,
    A::BuildAlloc: Clone,
{
    /// Returns a new box with a `clone()` of this box's contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(trivial_casts)]
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(5);
    /// let y = x.clone();
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // But they are unique objects
    /// assert_ne!(&*x as *const i32, &*y as *const i32);
    /// ```
    #[inline]
    fn clone(&self) -> Self {
        let mut b = self.build_alloc().clone();
        let old_ptr = self.ptr.cast();
        let old_layout = NonZeroLayout::for_value(self.as_ref());

        unsafe {
            let a = b.build_alloc_ref(old_ptr.into(), old_layout);
            self.clone_in(a)
        }
    }

    /// Copies `source`'s contents into `self` without creating a new allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = Box::new(5);
    /// let mut y = Box::new(10);
    /// let yp: *const i32 = &*y;
    ///
    /// y.clone_from(&x);
    ///
    /// // The value is the same
    /// assert_eq!(x, y);
    ///
    /// // And no allocation occurred
    /// assert_eq!(yp, &*y);
    /// ```
    #[inline]
    fn clone_from(&mut self, source: &Self) {
        (**self).clone_from(&(**source));
    }
}

#[allow(clippy::use_self)]
impl<T: Clone, A: AllocRef, B: AllocRef> CloneIn<B> for Box<T, A> {
    type Cloned = Box<T, B>;

    fn clone_in(&self, a: B) -> Self::Cloned
    where
        B: AllocRef<Error = !>,
    {
        Box::new_in(self.as_ref().clone(), a)
    }

    fn try_clone_in(&self, a: B) -> Result<Self::Cloned, B::Error> {
        Box::try_new_in(self.as_ref().clone(), a)
    }
}

impl<T: ?Sized + PartialEq, A: DeallocRef> PartialEq for Box<T, A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        PartialEq::eq(&**self, &**other)
    }
    #[allow(clippy::partialeq_ne_impl)]
    #[inline]
    fn ne(&self, other: &Self) -> bool {
        PartialEq::ne(&**self, &**other)
    }
}
impl<T: ?Sized + PartialOrd, A: DeallocRef> PartialOrd for Box<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
    #[inline]
    fn lt(&self, other: &Self) -> bool {
        PartialOrd::lt(&**self, &**other)
    }
    #[inline]
    fn le(&self, other: &Self) -> bool {
        PartialOrd::le(&**self, &**other)
    }
    #[inline]
    fn gt(&self, other: &Self) -> bool {
        PartialOrd::gt(&**self, &**other)
    }
    #[inline]
    fn ge(&self, other: &Self) -> bool {
        PartialOrd::ge(&**self, &**other)
    }
}
impl<T: ?Sized + Ord, A: DeallocRef> Ord for Box<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}
impl<T: ?Sized + Eq, A: DeallocRef> Eq for Box<T, A> {}

impl<T: ?Sized + Hash, A: DeallocRef> Hash for Box<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + Hasher, A: DeallocRef> Hasher for Box<T, A> {
    fn finish(&self) -> u64 {
        (**self).finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        (**self).write(bytes)
    }
    fn write_u8(&mut self, i: u8) {
        (**self).write_u8(i)
    }
    fn write_u16(&mut self, i: u16) {
        (**self).write_u16(i)
    }
    fn write_u32(&mut self, i: u32) {
        (**self).write_u32(i)
    }
    fn write_u64(&mut self, i: u64) {
        (**self).write_u64(i)
    }
    fn write_u128(&mut self, i: u128) {
        (**self).write_u128(i)
    }
    fn write_usize(&mut self, i: usize) {
        (**self).write_usize(i)
    }
    fn write_i8(&mut self, i: i8) {
        (**self).write_i8(i)
    }
    fn write_i16(&mut self, i: i16) {
        (**self).write_i16(i)
    }
    fn write_i32(&mut self, i: i32) {
        (**self).write_i32(i)
    }
    fn write_i64(&mut self, i: i64) {
        (**self).write_i64(i)
    }
    fn write_i128(&mut self, i: i128) {
        (**self).write_i128(i)
    }
    fn write_isize(&mut self, i: isize) {
        (**self).write_isize(i)
    }
}

impl<T, A: AllocRef<Error = !>> From<T> for Box<T, A>
where
    A: Default + AllocRef,
{
    /// Converts a generic type `T` into a `Box<T>`
    ///
    /// The conversion allocates on the heap and moves `t`
    /// from the stack into it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use alloc_wg::boxed::Box;
    ///
    /// let x = 5;
    /// let boxed = Box::new(5);
    ///
    /// assert_eq!(Box::from(x), boxed);
    /// ```
    fn from(t: T) -> Self {
        Self::new_in(t, A::default())
    }
}

impl<T: ?Sized, A: DeallocRef> From<Box<T, A>> for Pin<Box<T, A>> {
    /// Converts a `Box<T, A>` into a `Pin<Box<T, A>>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    fn from(boxed: Box<T, A>) -> Self {
        Box::into_pin(boxed)
    }
}

#[allow(clippy::use_self)]
impl<T: Copy, A> From<&[T]> for Box<[T], A>
where
    A: Default + AllocRef<Error = !>,
{
    /// Converts a `&[T]` into a `Box<[T], B>`
    ///
    /// This conversion allocates and performs a copy of `slice`.
    ///
    /// # Examples
    /// ```rust
    /// use alloc_wg::boxed::Box;
    ///
    /// // create a &[u8] which will be used to create a Box<[u8]>
    /// let slice: &[u8] = &[104, 101, 108, 108, 111];
    /// let boxed_slice: Box<[u8]> = Box::from(slice);
    ///
    /// println!("{:?}", boxed_slice);
    /// ```
    fn from(slice: &[T]) -> Self {
        let len = slice.len();
        let buf = RawVec::with_capacity_in(len, A::default());
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), buf.ptr(), len);
            buf.into_box().assume_init()
        }
    }
}

#[allow(clippy::use_self)]
impl<A> From<&str> for Box<str, A>
where
    A: Default + AllocRef<Error = !>,
{
    /// Converts a `&str` into a `Box<str>`
    ///
    /// This conversion allocates on the heap
    /// and performs a copy of `s`.
    ///
    /// # Examples
    /// ```rust
    /// use alloc_wg::boxed::Box;
    ///
    /// let boxed: Box<str> = Box::from("hello");
    /// println!("{}", boxed);
    /// ```
    #[inline]
    #[must_use]
    fn from(s: &str) -> Self {
        unsafe { from_boxed_utf8_unchecked(Box::from(s.as_bytes())) }
    }
}

#[allow(clippy::use_self)]
impl<A: DeallocRef> From<Box<str, A>> for Box<[u8], A> {
    /// Converts a `Box<str>>` into a `Box<[u8]>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    ///
    /// # Examples
    /// ```rust
    /// // create a Box<str> which will be used to create a Box<[u8]>
    /// let boxed: Box<str> = Box::from("hello");
    /// let boxed_str: Box<[u8]> = Box::from(boxed);
    ///
    /// // create a &[u8] which will be used to create a Box<[u8]>
    /// let slice: &[u8] = &[104, 101, 108, 108, 111];
    /// let boxed_slice = Box::from(slice);
    ///
    /// assert_eq!(boxed_slice, boxed_str);
    /// ```
    #[inline]
    fn from(s: Box<str, A>) -> Self {
        let (ptr, b) = Box::into_raw_alloc(s);
        unsafe { Self::from_raw_in(ptr as *mut [u8], b) }
    }
}

#[allow(clippy::use_self)]
impl<T, const N: usize> core::convert::TryFrom<Box<[T]>> for Box<[T; N]>
where
    [T; N]: core::array::LengthAtMost32,
{
    type Error = Box<[T]>;

    fn try_from(boxed_slice: Box<[T]>) -> Result<Self, Self::Error> {
        if boxed_slice.len() == N {
            Ok(unsafe { Self::from_raw(Box::into_raw(boxed_slice) as *mut [T; N]) })
        } else {
            Err(boxed_slice)
        }
    }
}

#[allow(clippy::use_self)]
impl<A: DeallocRef> Box<dyn Any, A> {
    #[inline]
    /// Attempt to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    pub fn downcast<T: Any>(self) -> Result<Box<T, A>, Box<dyn Any, A>> {
        if self.is::<T>() {
            unsafe {
                let (raw, b): (*mut dyn Any, _) = Self::into_raw_alloc(self);
                Ok(Box::from_raw_in(raw as *mut T, b))
            }
        } else {
            Err(self)
        }
    }
}

#[allow(clippy::use_self)]
impl<A: DeallocRef> Box<dyn Any + Send, A> {
    #[inline]
    /// Attempt to downcast the box to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    ///
    /// fn print_if_string(value: Box<dyn Any + Send>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Box::new(my_string));
    /// print_if_string(Box::new(0i8));
    /// ```
    pub fn downcast<T: Any>(self) -> Result<Box<T, A>, Box<dyn Any + Send, A>> {
        if self.is::<T>() {
            unsafe {
                let (raw, b): (*mut (dyn Any + Send), _) = Self::into_raw_alloc(self);
                Ok(Box::from_raw_in(raw as *mut T, b))
            }
        } else {
            Err(self)
        }
    }
}

impl<T: fmt::Display + ?Sized, A: DeallocRef> fmt::Display for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug + ?Sized, A: DeallocRef> fmt::Debug for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, A: DeallocRef> fmt::Pointer for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // It's not possible to extract the inner Uniq directly from the Box,
        // instead we cast it to a *const which aliases the Unique
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

impl<T: ?Sized, A: DeallocRef> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}
impl<T: ?Sized, A: DeallocRef> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized, A: DeallocRef> core::ops::Receiver for Box<T, A> {}

impl<I: Iterator + ?Sized, A: DeallocRef> Iterator for Box<I, A> {
    type Item = I::Item;
    fn next(&mut self) -> Option<I::Item> {
        (**self).next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (**self).size_hint()
    }
    fn last(self) -> Option<I::Item> {
        BoxIter::last(self)
    }
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth(n)
    }
}

trait BoxIter {
    type Item;
    fn last(self) -> Option<Self::Item>;
}

impl<I: Iterator + ?Sized, A: DeallocRef> BoxIter for Box<I, A> {
    type Item = I::Item;

    fn last(self) -> Option<I::Item> {
        #[inline]
        fn some<T>(_: Option<T>, x: T) -> Option<T> {
            Some(x)
        }

        self.fold(None, some)
    }
}

impl<I: DoubleEndedIterator + ?Sized, A: DeallocRef> DoubleEndedIterator for Box<I, A> {
    fn next_back(&mut self) -> Option<I::Item> {
        (**self).next_back()
    }
    fn nth_back(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth_back(n)
    }
}

impl<I: ExactSizeIterator + ?Sized, A: DeallocRef> ExactSizeIterator for Box<I, A> {
    fn len(&self) -> usize {
        (**self).len()
    }

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }
}

impl<I: FusedIterator + ?Sized, A: DeallocRef> FusedIterator for Box<I, A> {}

impl<Args, F: FnOnce<Args> + Copy + ?Sized, A: DeallocRef> FnOnce<Args> for Box<F, A> {
    type Output = <F as FnOnce<Args>>::Output;

    extern "rust-call" fn call_once(self, args: Args) -> Self::Output {
        <F as FnOnce<Args>>::call_once(*self, args)
    }
}

impl<Args, F: FnMut<Args> + Copy + ?Sized, A: DeallocRef> FnMut<Args> for Box<F, A> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output {
        <F as FnMut<Args>>::call_mut(self, args)
    }
}

impl<Args, F: Fn<Args> + Copy + ?Sized, A: DeallocRef> Fn<Args> for Box<F, A> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output {
        <F as Fn<Args>>::call(self, args)
    }
}

impl<T: ?Sized + core::marker::Unsize<U>, U: ?Sized, A: DeallocRef>
    core::ops::CoerceUnsized<Box<U, A>> for Box<T, A>
{
}

// DispatchFromDyn may only be implemented for ZSTs for now. Until this limitation is lifted,
// implement it only for Global, and System
macro_rules! impl_dispatch_from_dyn {
    ($alloc:ty) => {
        impl<T: ?Sized + core::marker::Unsize<U>, U: ?Sized>
            core::ops::DispatchFromDyn<Box<U, $alloc>> for Box<T, $alloc>
        {
        }
    };
}

impl_dispatch_from_dyn!(Global);
#[cfg(feature = "std")]
impl_dispatch_from_dyn!(std::alloc::System);

#[allow(clippy::items_after_statements)]
impl<T: Clone, A: Clone> Clone for Box<[T], A>
where
    A: AllocRef<Error = !>,
    A::BuildAlloc: Clone,
{
    fn clone(&self) -> Self {
        let mut b = self.build_alloc().clone();
        let old_ptr = self.ptr.cast();
        let old_layout = NonZeroLayout::for_value(self.as_ref());
        let a = unsafe { b.build_alloc_ref(old_ptr.into(), old_layout) };

        let mut new = BoxBuilder {
            data: RawVec::with_capacity_in(self.len(), a),
            len: 0,
        };

        let mut target = new.data.ptr();

        for item in self.iter() {
            unsafe {
                ptr::write(target, item.clone());
                target = target.offset(1);
            };

            new.len += 1;
        }

        return unsafe { new.into_box() };

        // Helper type for responding to panics correctly.
        struct BoxBuilder<T, A: DeallocRef> {
            data: RawVec<T, A>,
            len: usize,
        }

        impl<T, A: DeallocRef> BoxBuilder<T, A> {
            unsafe fn into_box(self) -> Box<[T], A> {
                let raw = ptr::read(&self.data);
                mem::forget(self);
                raw.into_box().assume_init()
            }
        }

        impl<T, A: DeallocRef> Drop for BoxBuilder<T, A> {
            fn drop(&mut self) {
                let mut data = self.data.ptr();
                let max = unsafe { data.add(self.len) };

                while data != max {
                    unsafe {
                        ptr::read(data);
                        data = data.offset(1);
                    }
                }
            }
        }
    }
}

impl<T: ?Sized, A: DeallocRef> borrow::Borrow<T> for Box<T, A> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, A: DeallocRef> borrow::BorrowMut<T> for Box<T, A> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized, A: DeallocRef> AsRef<T> for Box<T, A> {
    fn as_ref(&self) -> &T {
        &**self
    }
}
impl<T: ?Sized, A: DeallocRef> AsMut<T> for Box<T, A> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

/* Nota bene
 *
 *  We could have chosen not to add this impl, and instead have written a
 *  function of Pin<Box<T>> to Pin<T>. Such a function would not be sound,
 *  because Box<T> implements Unpin even when T does not, as a result of
 *  this impl.
 *
 *  We chose this API instead of the alternative for a few reasons:
 *      - Logically, it is helpful to understand pinning in regard to the
 *        memory region being pointed to. For this reason none of the
 *        standard library pointer types support projecting through a pin
 *        (Box<T> is the only pointer type in std for which this would be
 *        safe.)
 *      - It is in practice very useful to have Box<T> be unconditionally
 *        Unpin because of trait objects, for which the structural auto
 *        trait functionality does not apply (e.g., Box<dyn Foo> would
 *        otherwise not be Unpin).
 *
 *  Another type with the same semantics as Box but only a conditional
 *  implementation of `Unpin` (where `T: Unpin`) would be valid/safe, and
 *  could have a method to project a Pin<T> from it.
 */
impl<T: ?Sized, A: DeallocRef> Unpin for Box<T, A> {}

impl<F: ?Sized + Future + Unpin, A: DeallocRef> Future for Box<F, A> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        F::poll(Pin::new(&mut *self), cx)
    }
}

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}
