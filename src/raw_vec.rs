use crate::{
    alloc::{AllocRef, BuildAlloc, DeallocRef, Global, NonZeroLayout, ReallocRef},
    boxed::Box,
    collections::CollectionAllocErr::{self, AllocError, CapacityOverflow},
};
use core::{cmp, marker::PhantomData, mem, ptr, ptr::NonNull, slice};

/// A low-level utility for more ergonomically allocating, reallocating, and deallocating
/// a buffer of memory on the heap without having to worry about all the corner cases
/// involved. This type is excellent for building your own data structures like Vec and `VecDeque`.
/// In particular:
///
/// * Produces `Unique::empty()` on zero-sized types
/// * Produces `Unique::empty()` on zero-length allocations
/// * Catches all overflows in capacity computations (promotes them to "capacity overflow" panics)
/// * Guards against 32-bit systems allocating more than `isize::MAX` bytes
/// * Guards against overflowing your length
/// * Aborts on OOM or calls `handle_alloc_error` as applicable
/// * Avoids freeing `Unique::empty()`
/// * Contains a `ptr::Unique` and thus endows the user with all related benefits
///
/// This type does not in anyway inspect the memory that it manages. When dropped it *will*
/// free its memory, but it *won't* try to Drop its contents. It is up to the user of `RawVec`
/// to handle the actual things *stored* inside of a `RawVec`.
///
/// Note that a `RawVec` always forces its capacity to be `usize::MAX` for zero-sized types.
/// This enables you to use capacity growing logic catch the overflows in your length
/// that might occur with zero-sized types.
///
/// However this means that you need to be careful when round-tripping this type
/// with a `Box<[T]>`: `capacity()` won't yield the len. However `with_capacity`,
/// `shrink_to_fit`, and `from_box` will actually set `RawVec`'s private capacity
/// field. This allows zero-sized types to not be special-cased by consumers of
/// this type.
// Using `NonNull` + `PhantomData` instead of `Unique` to stay on stable as long as possible
pub struct RawVec<T, B: BuildAlloc = Global> {
    ptr: NonNull<T>,
    capacity: usize,
    build_alloc: B,
    _owned: PhantomData<T>,
}

impl<T> RawVec<T> {
    /// HACK(Centril): This exists because `#[unstable]` `const fn`s needn't conform
    /// to `min_const_fn` and so they cannot be called in `min_const_fn`s either.
    ///
    /// If you change `RawVec<T>::new` or dependencies, please take care to not
    /// introduce anything that would truly violate `min_const_fn`.
    ///
    /// NOTE: We could avoid this hack and check conformance with some
    /// `#[rustc_force_min_const_fn]` attribute which requires conformance
    /// with `min_const_fn` but does not necessarily allow calling it in
    /// `stable(...) const fn` / user code not enabling `foo` when
    /// `#[rustc_const_unstable(feature = "foo", ..)]` is present.
    pub const NEW: Self = Self::new();

    /// Creates the biggest possible `RawVec` (on the system heap)
    /// without allocating. If `T` has positive size, then this makes a
    /// `RawVec` with capacity `0`. If `T` is zero-sized, then it makes a
    /// `RawVec` with capacity `usize::MAX`. Useful for implementing
    /// delayed allocation.
    pub const fn new() -> Self {
        // FIXME(Centril): Reintegrate this with `fn new_in` when we can.

        // `!0` is `usize::MAX`. This branch should be stripped at compile time.
        // FIXME(mark-i-m): use this line when `if`s are allowed in `const`:
        // let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };

        // `Unique::empty()` doubles as "unallocated" and "zero-sized allocation".
        Self {
            ptr: NonNull::dangling(),
            // FIXME(mark-i-m): use `cap` when ifs are allowed in const
            capacity: [0, !0][(mem::size_of::<T>() == 0) as usize],
            build_alloc: Global,
            _owned: PhantomData,
        }
    }

    /// Creates a `RawVec` (on the system heap) with exactly the
    /// capacity and alignment requirements for a `[T; capacity]`. This is
    /// equivalent to calling `RawVec::new` when `capacity` is `0` or `T` is
    /// zero-sized. Note that if `T` is zero-sized this means you will
    /// *not* get a `RawVec` with the requested capacity.
    ///
    /// # Errors
    ///
    /// * `CapacityOverflow` if the requested capacity exceeds `usize::MAX` bytes.
    /// * `CapacityOverflow` on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    /// * `AllocError` on OOM
    #[inline]
    pub fn with_capacity(capacity: usize) -> Result<Self, CollectionAllocErr<Global>> {
        Self::with_capacity_in(capacity, Global)
    }

    /// Like `with_capacity`, but guarantees the buffer is zeroed.
    #[inline]
    pub fn with_capacity_zeroed(capacity: usize) -> Result<Self, CollectionAllocErr<Global>> {
        Self::with_capacity_zeroed_in(capacity, Global)
    }

    /// Reconstitutes a RawVec from a pointer, and capacity.
    ///
    /// # Safety
    ///
    /// The ptr must be allocated (via the default allocator `Global`), and with the
    /// given capacity. The capacity cannot exceed `isize::MAX` (only a concern on 32-bit systems).
    /// If the ptr and capacity come from a RawVec created with `Global`, then this is guaranteed.
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut T, capacity: usize) -> Self {
        Self::from_raw_parts_in(ptr, capacity, Global)
    }
}

impl<T, B: BuildAlloc> RawVec<T, B>
where
    B::Ref: AllocRef,
{
    /// Like `new` but parameterized over the choice of allocator for the returned `RawVec`.
    pub fn new_in(mut a: B::Ref) -> Self {
        let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };
        Self {
            ptr: NonNull::dangling(),
            capacity: cap,
            build_alloc: a.get_build_alloc(),
            _owned: PhantomData,
        }
    }

    #[inline]
    /// Like `with_capacity` but parameterized over the choice of allocator for the returned
    /// `RawVec`.
    pub fn with_capacity_in(capacity: usize, a: B::Ref) -> Result<Self, CollectionAllocErr<B>> {
        Self::allocate_in(capacity, false, a)
    }

    #[inline]
    /// Like `with_capacity_zeroed` but parameterized over the choice of allocator for the returned
    /// `RawVec`.
    pub fn with_capacity_zeroed_in(
        capacity: usize,
        a: B::Ref,
    ) -> Result<Self, CollectionAllocErr<B>> {
        Self::allocate_in(capacity, true, a)
    }

    fn allocate_in(
        capacity: usize,
        zeroed: bool,
        mut alloc: B::Ref,
    ) -> Result<Self, CollectionAllocErr<B>> {
        let elem_size = mem::size_of::<T>();

        let alloc_size = capacity.checked_mul(elem_size).ok_or(CapacityOverflow)?;
        alloc_guard(alloc_size)?;

        // handles ZSTs and `capacity = 0` alike
        let ptr = if alloc_size == 0 {
            NonNull::<T>::dangling()
        } else {
            let layout = unsafe {
                NonZeroLayout::from_size_align_unchecked(alloc_size, mem::align_of::<T>())
            };
            let result = if zeroed {
                alloc.alloc_zeroed(layout)
            } else {
                alloc.alloc(layout)
            };
            result.map_err(|inner| AllocError { layout, inner })?.cast()
        };

        unsafe {
            Ok(Self::from_raw_parts_in(
                ptr.as_ptr(),
                capacity,
                alloc.get_build_alloc(),
            ))
        }
    }
}

impl<T, B: BuildAlloc> RawVec<T, B> {
    /// Reconstitutes a `RawVec` from a pointer, capacity, and allocator.
    ///
    /// # Safety
    ///
    /// The ptr must be allocated (via the given allocator `build_alloc`), and with the given
    /// capacity. The capacity cannot exceed `isize::MAX` (only a concern on 32-bit systems).
    /// If the ptr and capacity come from a `RawVec` created via `build_alloc`, then this is
    /// guaranteed.
    pub unsafe fn from_raw_parts_in(ptr: *mut T, capacity: usize, build_alloc: B) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr),
            capacity,
            build_alloc,
            _owned: PhantomData,
        }
    }

    /// Gets a raw pointer to the start of the allocation. Note that this is
    /// Unique::empty() if `capacity = 0` or T is zero-sized. In the former case, you must
    /// be careful.
    pub fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Gets the capacity of the allocation.
    ///
    /// This will always be `usize::MAX` if `T` is zero-sized.
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        if mem::size_of::<T>() == 0 {
            !0
        } else {
            self.capacity
        }
    }

    /// Returns a shared reference to the alloc builder.
    pub fn build_alloc(&self) -> &B {
        &self.build_alloc
    }

    /// Returns a mutable reference to the alloc builder.
    pub fn build_alloc_mut(&mut self) -> &mut B {
        &mut self.build_alloc
    }

    /// Returns the allocator used by this `RawVec` and the used layout, if any.
    /// The layout is `None` if the capacity of this `RawVec` is `0` or if `T` is a zero sized type.
    pub fn alloc_ref(&mut self) -> (B::Ref, Option<NonZeroLayout>) {
        let size = mem::size_of::<T>() * self.capacity;
        let layout = if size == 0 {
            None
        } else {
            unsafe {
                Some(NonZeroLayout::from_size_align_unchecked(
                    size,
                    mem::align_of::<T>(),
                ))
            }
        };
        let ptr = self.ptr.cast();
        let alloc = unsafe { self.build_alloc_mut().build_alloc_ref(ptr, layout) };
        (alloc, layout)
    }
}

impl<T, B: BuildAlloc> From<Box<[T], B>> for RawVec<T, B> {
    fn from(slice: Box<[T], B>) -> Self {
        let len = slice.len();
        let (ptr, builder) = Box::into_raw_non_null_alloc(slice);
        Self {
            ptr: ptr.cast(),
            capacity: len,
            build_alloc: builder,
            _owned: PhantomData,
        }
    }
}

impl<T, B: BuildAlloc> From<RawVec<T, B>> for Box<[mem::MaybeUninit<T>], B> {
    fn from(vec: RawVec<T, B>) -> Self {
        unsafe {
            let slice: &mut [mem::MaybeUninit<T>] =
                slice::from_raw_parts_mut(vec.ptr() as _, vec.capacity);
            let output = Self::from_raw_in(slice, ptr::read(&vec.build_alloc));
            mem::forget(vec);
            output
        }
    }
}

// Copy for passing by value without warnings
#[derive(Copy, Clone)]
enum ReserveStrategy {
    Exact,
    Amortized,
}

impl<T, B: BuildAlloc> RawVec<T, B>
where
    B::Ref: ReallocRef,
{
    /// Calculates the buffer's new size given that it'll hold `used_capacity +
    /// needed_extra_capacity` elements. This logic is used in amortized reserve methods.
    /// Returns `(new_capacity, new_alloc_size)`.
    fn amortized_new_size(
        &self,
        used_capacity: usize,
        needed_extra_capacity: usize,
    ) -> Result<usize, CollectionAllocErr<B>> {
        // Nothing we can really do about these checks :(
        let required_cap = used_capacity
            .checked_add(needed_extra_capacity)
            .ok_or(CapacityOverflow)?;
        // Cannot overflow, because `cap <= isize::MAX`, and type of `cap` is `usize`.
        let double_cap = self.capacity * 2;
        // `double_cap` guarantees exponential growth.
        Ok(cmp::max(double_cap, required_cap))
    }

    /// Ensures that the buffer contains at least enough space to hold
    /// `used_capacity + needed_extra_capacity` elements. If it doesn't already have
    /// enough capacity, will reallocate enough space plus comfortable slack
    /// space to get amortized `O(1)` behavior. Will limit this behavior
    /// if it would needlessly cause itself to panic.
    ///
    /// If `used_capacity` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe
    /// code *you* write that relies on the behavior of this function may break.
    ///
    /// This is ideal for implementing a bulk-push operation like `extend`.
    ///
    /// # Errors
    ///
    /// * `CapacityOverflow` if the requested capacity exceeds `usize::MAX` bytes.
    /// * `CapacityOverflow` on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    /// * `AllocError` on OOM
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, collections::CollectionAllocErr, raw_vec::RawVec};
    /// use core::ptr;
    ///
    /// struct MyVec<T> {
    ///     buf: RawVec<T>,
    ///     len: usize,
    /// }
    ///
    /// impl<T: Clone> MyVec<T> {
    ///     pub fn push_all(&mut self, elems: &[T]) -> Result<(), CollectionAllocErr<Global>> {
    ///         self.buf.reserve(self.len, elems.len())?;
    ///         // reserve would have aborted or panicked if the len exceeded
    ///         // `isize::MAX` so this is safe to do unchecked now.
    ///         for x in elems {
    ///             unsafe {
    ///                 ptr::write(self.buf.ptr().add(self.len), x.clone());
    ///             }
    ///             self.len += 1;
    ///         }
    ///         Ok(())
    ///     }
    /// }
    /// # fn main() -> Result<(), CollectionAllocErr<Global>> {
    /// #   let mut vector = MyVec { buf: RawVec::new(), len: 0 };
    /// #   vector.push_all(&[1, 3, 5, 7, 9])?;
    /// #   Ok(())
    /// # }
    /// ```
    pub fn reserve(
        &mut self,
        used_capacity: usize,
        needed_extra_capacity: usize,
    ) -> Result<(), CollectionAllocErr<B>> {
        self.reserve_internal(
            used_capacity,
            needed_extra_capacity,
            ReserveStrategy::Amortized,
        )
    }

    /// Attempts to ensure that the buffer contains at least enough space to hold
    /// `used_capacity + needed_extra_capacity` elements. If it doesn't already have
    /// enough capacity, will reallocate in place enough space plus comfortable slack
    /// space to get amortized `O(1)` behavior. Will limit this behaviour
    /// if it would needlessly cause itself to panic.
    ///
    /// If `used_capacity` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe
    /// code *you* write that relies on the behavior of this function may break.
    ///
    /// Returns `true` if the reallocation attempt has succeeded.
    ///
    /// # Errors
    ///
    /// * `CapacityOverflow` if the requested capacity exceeds `usize::MAX` bytes.
    /// * `CapacityOverflow` on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    /// * `AllocError` on OOM
    pub fn reserve_exact(
        &mut self,
        used_capacity: usize,
        needed_extra_capacity: usize,
    ) -> Result<(), CollectionAllocErr<B>> {
        self.reserve_internal(used_capacity, needed_extra_capacity, ReserveStrategy::Exact)
    }

    /// Shrinks the allocation down to the specified amount. If the given amount
    /// is 0, actually completely deallocates.
    ///
    /// # Panics
    ///
    /// Panics if the given amount is *larger* than the current capacity.
    ///
    /// # Errors
    ///
    /// * `AllocError` on OOM
    pub fn shrink_to_fit(&mut self, amount: usize) -> Result<(), CollectionAllocErr<B>> {
        let elem_size = mem::size_of::<T>();

        // Set the `cap` because they might be about to promote to a `Box<[T]>`
        if elem_size == 0 {
            self.capacity = amount;
            return Ok(());
        }

        // This check is my waterloo; it's the only thing Vec wouldn't have to do.
        assert!(
            self.capacity >= amount,
            "Tried to shrink to a larger capacity"
        );

        if amount == 0 {
            // We want to create a new zero-length vector within the
            // same allocator.  We use ptr::write to avoid an
            // erroneous attempt to drop the contents, and we use
            // ptr::read to sidestep condition against destructuring
            // types that implement Drop.

            unsafe {
                let build_alloc = ptr::read(self.build_alloc());
                self.dealloc_buffer();
                ptr::write(
                    self,
                    Self::from_raw_parts_in(NonNull::dangling().as_ptr(), 0, build_alloc),
                );
            }
        } else if self.capacity != amount {
            unsafe {
                // We know here that our `amount` is greater than zero. This
                // implies, via the assert above, that capacity is also greater
                // than zero, which means that we've got a current layout that
                // "fits"
                //
                // We also know that `self.cap` is greater than `amount`, and
                // consequently we don't need runtime checks for creating either
                // layout
                let old_size = elem_size * self.capacity;
                let new_size = elem_size * amount;
                let align = mem::align_of::<T>();
                let old_layout = NonZeroLayout::from_size_align_unchecked(old_size, align);
                let ptr = self.ptr.cast();
                self.build_alloc
                    .build_alloc_ref(ptr, Some(old_layout))
                    .realloc(ptr, old_layout, new_size)
                    .map_err(|inner| AllocError {
                        layout: NonZeroLayout::from_size_align_unchecked(new_size, align),
                        inner,
                    })?;
            }
            self.capacity = amount;
        }
        Ok(())
    }

    fn reserve_internal(
        &mut self,
        used_capacity: usize,
        needed_extra_capacity: usize,
        strategy: ReserveStrategy,
    ) -> Result<(), CollectionAllocErr<B>> {
        unsafe {
            // NOTE: we don't early branch on ZSTs here because we want this
            // to actually catch "asking for more than usize::MAX" in that case.
            // If we make it past the first branch then we are guaranteed to
            // panic.

            // Don't actually need any more capacity.
            // Wrapping in case they gave a bad `used_capacity`.
            if self.capacity().wrapping_sub(used_capacity) >= needed_extra_capacity {
                return Ok(());
            }

            // Nothing we can really do about these checks :(
            let new_cap = match strategy {
                ReserveStrategy::Exact => used_capacity
                    .checked_add(needed_extra_capacity)
                    .ok_or(CapacityOverflow)?,
                ReserveStrategy::Amortized => {
                    self.amortized_new_size(used_capacity, needed_extra_capacity)?
                }
            };
            let new_layout = NonZeroLayout::array::<T>(new_cap)?;

            alloc_guard(new_layout.size())?;

            let result = match self.alloc_ref() {
                (mut alloc, Some(layout)) => {
                    debug_assert_eq!(new_layout.align(), layout.align());
                    alloc.realloc(self.ptr.cast(), layout, new_layout.size())
                }
                (mut alloc, None) => alloc.alloc(new_layout),
            };

            self.ptr = result
                .map_err(|inner| AllocError {
                    layout: new_layout,
                    inner,
                })?
                .cast();
            self.capacity = new_cap;

            Ok(())
        }
    }
}

impl<T, B: BuildAlloc> RawVec<T, B> {
    /// Frees the memory owned by the RawVec *without* trying to Drop its contents.
    pub unsafe fn dealloc_buffer(&mut self) {
        if let (mut alloc, Some(layout)) = self.alloc_ref() {
            alloc.dealloc(self.ptr.cast(), layout)
        }
    }
}

#[cfg(feature = "dropck_eyepatch")]
unsafe impl<#[may_dangle] T, B: BuildAlloc> Drop for RawVec<T, B> {
    /// Frees the memory owned by the RawVec *without* trying to Drop its contents.
    fn drop(&mut self) {
        unsafe {
            self.dealloc_buffer();
        }
    }
}

#[cfg(not(feature = "dropck_eyepatch"))]
impl<T, B: BuildAlloc> Drop for RawVec<T, B> {
    /// Frees the memory owned by the RawVec *without* trying to Drop its contents.
    fn drop(&mut self) {
        unsafe {
            self.dealloc_buffer();
        }
    }
}

// We need to guarantee the following:
// * We don't ever allocate `> isize::MAX` byte-size objects
// * We don't overflow `usize::MAX` and actually allocate too little
//
// On 64-bit we just need to check for overflow since trying to allocate
// `> isize::MAX` bytes will surely fail. On 32-bit and 16-bit we need to add
// an extra guard for this in case we're running on a platform which can use
// all 4GB in user-space. e.g., PAE or x32

#[inline]
#[allow(clippy::cast_sign_loss)]
fn alloc_guard<B: BuildAlloc>(alloc_size: usize) -> Result<(), CollectionAllocErr<B>>
where
    B::Ref: AllocRef,
{
    if mem::size_of::<usize>() < 8 && alloc_size > isize::max_value() as usize {
        Err(CapacityOverflow)
    } else {
        Ok(())
    }
}
