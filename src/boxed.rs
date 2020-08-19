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
    alloc::{handle_alloc_error, AllocRef, BuildAllocRef, Global, Layout},
    clone::CloneIn,
    ptr::Unique,
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
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::{self, NonNull},
    task::{Context, Poll},
};

/// A pointer type for heap allocation.
///
/// See the [module-level documentation](index.html) for more.
pub struct Box<T: ?Sized, A: BuildAllocRef = Global> {
    ptr: Unique<T>,
    alloc: A,
}

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
        Self::new_in(x, Global)
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
    pub fn new_uninit() -> Box<MaybeUninit<T>> {
        Self::new_uninit_in(Global)
    }

    /// Constructs a new `Pin<Box<T>>`. If `T` does not implement `Unpin`, then
    /// `x` will be pinned in memory and unable to be moved.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn pin(x: T) -> Pin<Self> {
        Self::pin_in(x, Global)
    }
}

#[allow(clippy::use_self)]
impl<T, A: BuildAllocRef> Box<T, A> {
    /// Allocates memory with the given allocator and then places `x` into it.
    ///
    /// This doesn't actually allocate if `T` is zero-sized.
    ///
    /// # Example
    ///
    /// ```
    /// #![feature(allocator_api)]
    /// use alloc_wg::{alloc::Global, boxed::Box};
    ///
    /// # #[allow(unused_variables)]
    /// let five = Box::new_in(5, Global);
    /// ```
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn new_in(x: T, alloc_builder: A) -> Self {
        let mut boxed = Self::new_uninit_in(alloc_builder);
        unsafe {
            boxed.ptr.as_mut().write(x);
            boxed.assume_init()
        }
    }

    /// Constructs a new box with uninitialized contents in a specified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// #![feature(allocator_api)]
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
    pub fn new_uninit_in(mut alloc_builder: A) -> Box<MaybeUninit<T>, A> {
        let layout = Layout::new::<T>();
        let mut alloc = unsafe { alloc_builder.build_alloc_ref(NonNull::dangling(), layout) };
        let ptr = alloc
            .alloc(Layout::new::<MaybeUninit<T>>())
            .unwrap_or_else(|_| handle_alloc_error(layout));
        unsafe { Box::from_raw_in(ptr.as_mut_ptr().cast(), alloc_builder) }
    }

    /// Constructs a new `Pin<Box<T, A>>` with the specified allocator. If `T` does not implement
    /// `Unpin`, then `x` will be pinned in memory and unable to be moved.
    #[allow(clippy::inline_always)]
    #[inline(always)]
    pub fn pin_in(x: T, a: A) -> Pin<Self> {
        Pin::from(Self::new_in(x, a))
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
    pub fn new_uninit_slice(len: usize) -> Box<[MaybeUninit<T>]> {
        Self::new_uninit_slice_in(len, Global)
    }
}

#[allow(clippy::use_self)]
impl<T, A: BuildAllocRef> Box<[T], A> {
    /// Construct a new boxed slice with uninitialized contents with the spoecified allocator.
    ///
    /// # Example
    ///
    /// ```
    /// #![feature(allocator_api)]
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
    pub fn new_uninit_slice_in(len: usize, a: A) -> Box<[MaybeUninit<T>], A> {
        unsafe { RawVec::with_capacity_in(len, a).into_box(len) }
    }
}

#[allow(clippy::use_self)]
impl<T, A: BuildAllocRef> Box<MaybeUninit<T>, A> {
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
        let (ptr, alloc) = Self::into_raw_alloc(self);
        Box::from_raw_in((*ptr).as_mut_ptr(), alloc)
    }
}

#[allow(clippy::use_self)]
impl<T, A: BuildAllocRef> Box<[MaybeUninit<T>], A> {
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
        Self::from_raw_in(raw, Global)
    }
}

impl<T: ?Sized, A: BuildAllocRef> Box<T, A> {
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
    /// #![feature(allocator_api)]
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
    pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Self {
        Self {
            ptr: Unique::new_unchecked(raw),
            alloc,
        }
    }

    /// Returns a shared reference to the associated `BuildAlloc`
    pub fn build_alloc(&self) -> &A {
        &self.alloc
    }

    /// Returns a mutable reference to the associated `BuildAlloc`
    pub fn build_alloc_mut(&mut self) -> &mut A {
        &mut self.alloc
    }

    /// Returns a shared reference to the allocator.
    pub fn alloc_ref(&self) -> &A {
        &self.alloc
    }

    /// Returns a mutable reference to the allocator.
    pub fn alloc_ref_mut(&mut self) -> &mut A {
        &mut self.alloc
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
    pub fn into_raw_alloc(b: Self) -> (*mut T, A) {
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
    pub fn into_raw_non_null_alloc(b: Self) -> (NonNull<T>, A) {
        let (unique, alloc) = Self::into_unique_alloc(b);
        (unique.into(), alloc)
    }

    #[inline]
    #[doc(hidden)]
    pub fn into_unique(b: Self) -> Unique<T> {
        Self::into_unique_alloc(b).0
    }

    #[inline]
    #[doc(hidden)]
    pub fn into_unique_alloc(mut b: Self) -> (Unique<T>, A) {
        let ptr = b.ptr;
        let alloc = unsafe { ptr::read(b.alloc_ref_mut()) };
        mem::forget(b);

        // Box is kind-of a library type, but recognized as a "unique pointer" by
        // Stacked Borrows.  This function here corresponds to "reborrowing to
        // a raw pointer", but there is no actual reborrow here -- so
        // without some care, the pointer we are returning here still carries
        // the tag of `b`, with `Unique` permission.
        // We round-trip through a mutable reference to avoid that.
        (ptr, alloc)
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

fn drop_box<T: ?Sized, A: BuildAllocRef>(boxed: &mut Box<T, A>) {
    unsafe {
        let layout = Layout::for_value(boxed.as_ref());
        let ptr = NonNull::from(boxed.ptr);
        let mut alloc = boxed.build_alloc_mut().build_alloc_ref(ptr.cast(), layout);
        ptr::drop_in_place(ptr.as_ptr());
        alloc.dealloc(ptr.cast(), layout);
    }
}

unsafe impl<#[may_dangle] T: ?Sized, A: BuildAllocRef> Drop for Box<T, A> {
    fn drop(&mut self) {
        drop_box(self);
    }
}

impl<T, A> Default for Box<T, A>
where
    T: Default,
    A: Default + BuildAllocRef,
{
    #[must_use]
    fn default() -> Self {
        Self::new_in(T::default(), A::default())
    }
}

#[allow(clippy::use_self)]
impl<T, A: BuildAllocRef> Default for Box<[T], A>
where
    A: Default,
{
    #[must_use]
    fn default() -> Self {
        Box::<[T; 0], A>::new_in([], A::default())
    }
}

#[inline]
unsafe fn from_boxed_utf8_unchecked<A: BuildAllocRef>(v: Box<[u8], A>) -> Box<str, A> {
    let (ptr, b) = Box::into_raw_alloc(v);
    Box::from_raw_in(ptr as *mut str, b)
}

#[allow(clippy::use_self)]
impl<A> Default for Box<str, A>
where
    A: Default + BuildAllocRef,
{
    #[must_use]
    fn default() -> Self {
        unsafe { from_boxed_utf8_unchecked(Box::default()) }
    }
}

impl<T: Clone, A: BuildAllocRef + Clone> Clone for Box<T, A> {
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
        self.clone_in(self.alloc.clone())
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
impl<T: Clone, A: BuildAllocRef, B: BuildAllocRef> CloneIn<B> for Box<T, A> {
    type Cloned = Box<T, B>;

    fn clone_in(&self, a: B) -> Self::Cloned {
        Box::new_in(self.as_ref().clone(), a)
    }
}

impl<T: ?Sized + PartialEq, A: BuildAllocRef> PartialEq for Box<T, A> {
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
impl<T: ?Sized + PartialOrd, A: BuildAllocRef> PartialOrd for Box<T, A> {
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
impl<T: ?Sized + Ord, A: BuildAllocRef> Ord for Box<T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}
impl<T: ?Sized + Eq, A: BuildAllocRef> Eq for Box<T, A> {}

impl<T: ?Sized + Hash, A: BuildAllocRef> Hash for Box<T, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + Hasher, A: BuildAllocRef> Hasher for Box<T, A> {
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

impl<T, A> From<T> for Box<T, A>
where
    A: Default + BuildAllocRef,
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

impl<T: ?Sized, A: BuildAllocRef> From<Box<T, A>> for Pin<Box<T, A>> {
    /// Converts a `Box<T, A>` into a `Pin<Box<T, A>>`
    ///
    /// This conversion does not allocate on the heap and happens in place.
    fn from(boxed: Box<T, A>) -> Self {
        Box::into_pin(boxed)
    }
}

#[allow(clippy::use_self)]
impl<T: Copy, A: BuildAllocRef> From<&[T]> for Box<[T], A>
where
    A: Default,
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
            buf.into_box(slice.len()).assume_init()
        }
    }
}

#[allow(clippy::use_self)]
impl<A: BuildAllocRef> From<&str> for Box<str, A>
where
    A: Default,
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
impl<A: BuildAllocRef> From<Box<str, A>> for Box<[u8], A> {
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
impl<T, const N: usize> core::convert::TryFrom<Box<[T]>> for Box<[T; N]> {
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
impl<A: BuildAllocRef> Box<dyn Any, A> {
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
impl<A: BuildAllocRef> Box<dyn Any + Send, A> {
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

impl<T: fmt::Display + ?Sized, A: BuildAllocRef> fmt::Display for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: fmt::Debug + ?Sized, A: BuildAllocRef> fmt::Debug for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized, A: BuildAllocRef> fmt::Pointer for Box<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // It's not possible to extract the inner Uniq directly from the Box,
        // instead we cast it to a *const which aliases the Unique
        let ptr: *const T = &**self;
        fmt::Pointer::fmt(&ptr, f)
    }
}

impl<T: ?Sized, A: BuildAllocRef> Deref for Box<T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}
impl<T: ?Sized, A: BuildAllocRef> DerefMut for Box<T, A> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T: ?Sized, A: BuildAllocRef> core::ops::Receiver for Box<T, A> {}

impl<I: Iterator + ?Sized, A: BuildAllocRef> Iterator for Box<I, A> {
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

impl<I: Iterator + ?Sized, A: BuildAllocRef> BoxIter for Box<I, A> {
    type Item = I::Item;

    fn last(self) -> Option<I::Item> {
        #[inline]
        #[allow(clippy::missing_const_for_fn)]
        fn some<T>(_: Option<T>, x: T) -> Option<T> {
            Some(x)
        }

        self.fold(None, some)
    }
}

impl<I: DoubleEndedIterator + ?Sized, A: BuildAllocRef> DoubleEndedIterator for Box<I, A> {
    fn next_back(&mut self) -> Option<I::Item> {
        (**self).next_back()
    }
    fn nth_back(&mut self, n: usize) -> Option<I::Item> {
        (**self).nth_back(n)
    }
}

impl<I: ExactSizeIterator + ?Sized, A: BuildAllocRef> ExactSizeIterator for Box<I, A> {
    fn len(&self) -> usize {
        (**self).len()
    }

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }
}

impl<I: FusedIterator + ?Sized, A: BuildAllocRef> FusedIterator for Box<I, A> {}

impl<Args, F: FnOnce<Args> + Copy + ?Sized, A: BuildAllocRef> FnOnce<Args> for Box<F, A> {
    type Output = <F as FnOnce<Args>>::Output;

    extern "rust-call" fn call_once(self, args: Args) -> Self::Output {
        <F as FnOnce<Args>>::call_once(*self, args)
    }
}

impl<Args, F: FnMut<Args> + Copy + ?Sized, A: BuildAllocRef> FnMut<Args> for Box<F, A> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output {
        <F as FnMut<Args>>::call_mut(self, args)
    }
}

impl<Args, F: Fn<Args> + Copy + ?Sized, A: BuildAllocRef> Fn<Args> for Box<F, A> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output {
        <F as Fn<Args>>::call(self, args)
    }
}

impl<T: ?Sized + core::marker::Unsize<U>, U: ?Sized, A: BuildAllocRef>
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
    A: BuildAllocRef,
{
    fn clone(&self) -> Self {
        let mut new = BoxBuilder {
            data: RawVec::with_capacity_in(self.len(), self.alloc_ref().clone()),
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
        struct BoxBuilder<T, A: BuildAllocRef> {
            data: RawVec<T, A>,
            len: usize,
        }

        impl<T, A: BuildAllocRef> BoxBuilder<T, A> {
            unsafe fn into_box(self) -> Box<[T], A> {
                let raw = ptr::read(&self.data);
                let len = self.len;
                mem::forget(self);
                raw.into_box(len).assume_init()
            }
        }

        impl<T, A: BuildAllocRef> Drop for BoxBuilder<T, A> {
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

impl<T: ?Sized, A: BuildAllocRef> borrow::Borrow<T> for Box<T, A> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, A: BuildAllocRef> borrow::BorrowMut<T> for Box<T, A> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized, A: BuildAllocRef> AsRef<T> for Box<T, A> {
    fn as_ref(&self) -> &T {
        &**self
    }
}
impl<T: ?Sized, A: BuildAllocRef> AsMut<T> for Box<T, A> {
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
impl<T: ?Sized, A: BuildAllocRef> Unpin for Box<T, A> {}

impl<F: ?Sized + Future + Unpin, A: BuildAllocRef> Future for Box<F, A> {
    type Output = F::Output;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        F::poll(Pin::new(&mut *self), cx)
    }
}
