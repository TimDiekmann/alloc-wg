//! A contiguous growable array type with heap-allocated contents, written
//! `Vec<T>`.
//!
//! Vectors have `O(1)` indexing, amortized `O(1)` push (to the end) and
//! `O(1)` pop (from the end).
//!
//! # Examples
//!
//! You can explicitly create a [`Vec<T>`] with [`new`]:
//!
//! ```
//! # #![allow(unused_variables)]
//! use alloc_wg::vec::Vec;
//!
//! let v: Vec<i32> = Vec::new();
//! ```
//!
//! ...or by using the [`vec!`] macro:
//!
//! ```
//! # #![allow(unused_variables)]
//! use alloc_wg::{vec, vec::Vec};
//!
//! let v: Vec<i32> = Vec::new();
//!
//! let v = vec![1, 2, 3, 4, 5];
//!
//! let v = vec![0; 10]; // ten zeroes
//! ```
//!
//! You can [`push`] values onto the end of a vector (which will grow the vector
//! as needed):
//!
//! ```
//! use alloc_wg::vec;
//!
//! let mut v = vec![1, 2];
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! # #![allow(unused_variables)]
//! use alloc_wg::vec;
//!
//! let mut v = vec![1, 2];
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the [`Index`] and [`IndexMut`] traits):
//!
//! ```
//! # #![allow(unused_variables)]
//! use alloc_wg::vec;
//!
//! let mut v = vec![1, 2, 3];
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```
//!
//! [`Vec<T>`]: crate::vec::Vec
//! [`new`]: crate::vec::Vec::new()
//! [`push`]: crate::vec::Vec::push()
//! [`Index`]: core::ops::Index
//! [`IndexMut`]: core::ops::IndexMut
//! [`vec!`]: ../macro.vec.html

use crate::{
    alloc::{
        handle_alloc_error,
        AllocRef,
        BuildAllocRef,
        DeallocRef,
        Global,
        NonZeroLayout,
        ReallocRef,
    },
    boxed::Box,
    clone::CloneIn,
    collections::CollectionAllocErr,
    iter::{FromIteratorIn, TryExtend},
    raw_vec::RawVec,
};
use core::{
    cmp::{self, Ordering},
    convert::TryFrom,
    fmt,
    hash::{self, Hash},
    intrinsics::assume,
    iter::{FromIterator, FusedIterator, TrustedLen},
    mem,
    ops::{
        self,
        Bound::{Excluded, Included, Unbounded},
        Index,
        IndexMut,
        RangeBounds,
    },
    ptr::{self, NonNull},
    slice::{self, SliceIndex},
};

/// A contiguous growable array type, written `Vec<T>` but pronounced 'vector'.
///
/// # Examples
///
/// ```
/// use alloc_wg::vec::Vec;
///
/// let mut vec = Vec::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3].iter().cloned());
///
/// for x in &vec {
///     println!("{}", x);
/// }
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
///
/// The [`vec!`] macro is provided to make initialization more convenient:
///
/// ```
/// use alloc_wg::vec;
///
/// let mut vec = vec![1, 2, 3];
/// vec.push(4);
/// assert_eq!(vec, [1, 2, 3, 4]);
/// ```
///
/// It can also initialize each element of a `Vec<T>` with a given value.
/// This may be more efficient than performing allocation and initialization
/// in separate steps, especially when initializing a vector of zeros:
///
/// ```
/// use alloc_wg::{vec, vec::Vec};
///
/// let vec = vec![0; 5];
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
///
/// // The following is equivalent, but potentially slower:
/// let mut vec1 = Vec::with_capacity(5);
/// vec1.resize(5, 0);
/// ```
///
/// Use a `Vec<T>` as an efficient stack:
///
/// ```
/// use alloc_wg::vec::Vec;
///
/// let mut stack = Vec::new();
///
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
///
/// while let Some(top) = stack.pop() {
///     // Prints 3, 2, 1
///     println!("{}", top);
/// }
/// ```
///
/// # Indexing
///
/// The `Vec` type allows to access values by index, because it implements the
/// [`Index`] trait. An example will be more explicit:
///
/// ```
/// use alloc_wg::vec;
///
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[1]); // it will display '2'
/// ```
///
/// However be careful: if you try to access an index which isn't in the `Vec`,
/// your software will panic! You cannot do this:
///
/// ```should_panic
/// use alloc_wg::vec;
///
/// let v = vec![0, 2, 4, 6];
/// println!("{}", v[6]); // it will panic!
/// ```
///
/// Use [`get`] and [`get_mut`] if you want to check whether the index is in
/// the `Vec`.
///
/// # Slicing
///
/// A `Vec` can be mutable. Slices, on the other hand, are read-only objects.
/// To get a slice, use `&`. Example:
///
/// ```
/// # #![allow(unused_variables)]
/// use alloc_wg::vec;
///
/// fn read_slice(slice: &[usize]) {
///     // ...
/// }
///
/// let v = vec![0, 1];
/// read_slice(&v);
///
/// // ... and that's all!
/// // you can also do it like this:
/// let x: &[usize] = &v;
/// ```
///
/// In Rust, it's more common to pass slices as arguments rather than vectors
/// when you just want to provide a read access. The same goes for [`String`] and
/// [`&str`].
///
/// # Capacity and reallocation
///
/// The capacity of a vector is the amount of space allocated for any future
/// elements that will be added onto the vector. This is not to be confused with
/// the *length* of a vector, which specifies the number of actual elements
/// within the vector. If a vector's length exceeds its capacity, its capacity
/// will automatically be increased, but its elements will have to be
/// reallocated.
///
/// For example, a vector with capacity 10 and length 0 would be an empty vector
/// with space for 10 more elements. Pushing 10 or fewer elements onto the
/// vector will not change its capacity or cause reallocation to occur. However,
/// if the vector's length is increased to 11, it will have to reallocate, which
/// can be slow. For this reason, it is recommended to use [`Vec::with_capacity`]
/// whenever possible to specify how big the vector is expected to get.
///
/// # Guarantees
///
/// Due to its incredibly fundamental nature, `Vec` makes a lot of guarantees
/// about its design. This ensures that it's as low-overhead as possible in
/// the general case, and can be correctly manipulated in primitive ways
/// by unsafe code. Note that these guarantees refer to an unqualified `Vec<T>`.
/// If additional type parameters are added (e.g., to support custom allocators),
/// overriding their defaults may change the behavior.
///
/// Most fundamentally, `Vec` is and always will be a (pointer, capacity, length)
/// triplet. No more, no less. The order of these fields is completely
/// unspecified, and you should use the appropriate methods to modify these.
/// The pointer will never be null, so this type is null-pointer-optimized.
///
/// However, the pointer may not actually point to allocated memory. In particular,
/// if you construct a `Vec` with capacity 0 via [`Vec::new`], [`vec![]`][`vec!`],
/// [`Vec::with_capacity(0)`][`Vec::with_capacity`], or by calling [`shrink_to_fit`]
/// on an empty Vec, it will not allocate memory. Similarly, if you store zero-sized
/// types inside a `Vec`, it will not allocate space for them. *Note that in this case
/// the `Vec` may not report a [`capacity`] of 0*. `Vec` will allocate if and only
/// if [`mem::size_of::<T>`]`() * capacity() > 0`. In general, `Vec`'s allocation
/// details are very subtle &mdash; if you intend to allocate memory using a `Vec`
/// and use it for something else (either to pass to unsafe code, or to build your
/// own memory-backed collection), be sure to deallocate this memory by using
/// `from_raw_parts` to recover the `Vec` and then dropping it.
///
/// If a `Vec` *has* allocated memory, then the memory it points to is on the heap
/// (as defined by the allocator Rust is configured to use by default), and its
/// pointer points to [`len`] initialized, contiguous elements in order (what
/// you would see if you coerced it to a slice), followed by [`capacity`]` -
/// `[`len`] logically uninitialized, contiguous elements.
///
/// `Vec` will never perform a "small optimization" where elements are actually
/// stored on the stack for two reasons:
///
/// * It would make it more difficult for unsafe code to correctly manipulate
///   a `Vec`. The contents of a `Vec` wouldn't have a stable address if it were
///   only moved, and it would be more difficult to determine if a `Vec` had
///   actually allocated memory.
///
/// * It would penalize the general case, incurring an additional branch
///   on every access.
///
/// `Vec` will never automatically shrink itself, even if completely empty. This
/// ensures no unnecessary allocations or deallocations occur. Emptying a `Vec`
/// and then filling it back up to the same [`len`] should incur no calls to
/// the allocator. If you wish to free up unused memory, use
/// [`shrink_to_fit`][`shrink_to_fit`].
///
/// [`push`] and [`insert`] will never (re)allocate if the reported capacity is
/// sufficient. [`push`] and [`insert`] *will* (re)allocate if
/// [`len`]` == `[`capacity`]. That is, the reported capacity is completely
/// accurate, and can be relied on. It can even be used to manually free the memory
/// allocated by a `Vec` if desired. Bulk insertion methods *may* reallocate, even
/// when not necessary.
///
/// `Vec` does not guarantee any particular growth strategy when reallocating
/// when full, nor when [`reserve`] is called. The current strategy is basic
/// and it may prove desirable to use a non-constant growth factor. Whatever
/// strategy is used will of course guarantee `O(1)` amortized [`push`].
///
/// `vec![x; n]`, `vec![a, b, c, d]`, and
/// [`Vec::with_capacity(n)`][`Vec::with_capacity`], will all produce a `Vec`
/// with exactly the requested capacity. If [`len`]` == `[`capacity`],
/// (as is the case for the [`vec!`] macro), then a `Vec<T>` can be converted to
/// and from a [`Box<[T]>`][owned slice] without reallocating or moving the elements.
///
/// `Vec` will not specifically overwrite any data that is removed from it,
/// but also won't specifically preserve it. Its uninitialized memory is
/// scratch space that it may use however it wants. It will generally just do
/// whatever is most efficient or otherwise easy to implement. Do not rely on
/// removed data to be erased for security purposes. Even if you drop a `Vec`, its
/// buffer may simply be reused by another `Vec`. Even if you zero a `Vec`'s memory
/// first, that may not actually happen because the optimizer does not consider
/// this a side-effect that must be preserved. There is one case which we will
/// not break, however: using `unsafe` code to write to the excess capacity,
/// and then increasing the length to match, is always valid.
///
/// `Vec` does not currently guarantee the order in which elements are dropped.
/// The order has changed in the past and may change again.
///
/// [`vec!`]: ../macro.vec.html
/// [`get`]: struct.Vec.html#method.get
/// [`get_mut`]: struct.Vec.html#method.get_mut
/// [`Index`]: core::ops::Index
/// [`String`]: liballoc::string::String
/// [`&str`]: str
/// [`Vec::with_capacity`]: Self::with_capacity()
/// [`Vec::new`]: Self::new()
/// [`shrink_to_fit`]: Self::shrink_to_fit()
/// [`capacity`]: Self::capacity()
/// [`mem::size_of::<T>`]: core::mem::size_of()
/// [`len`]: struct.Vec.html#method.len
/// [`push`]: Self::push()
/// [`insert`]: Self::insert()
/// [`reserve`]: Self::reserve
/// [owned slice]: crate::boxed::Box
pub struct Vec<T, A: DeallocRef = Global> {
    buf: RawVec<T, A>,
    len: usize,
}

////////////////////////////////////////////////////////////////////////////////
// Inherent methods
////////////////////////////////////////////////////////////////////////////////

impl<T> Vec<T> {
    /// Constructs a new, empty `Vec<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use alloc_wg::vec::Vec;
    ///
    /// let vec: Vec<i32> = Vec::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            buf: RawVec::NEW,
            len: 0,
        }
    }

    /// Constructs a new, empty `Vec<T>` with the specified capacity.
    ///
    /// The vector will be able to hold exactly `capacity` elements without
    /// reallocating. If `capacity` is 0, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// *capacity* specified, the vector will have a zero *length*. For an
    /// explanation of the difference between length and capacity, see
    /// *[Capacity and reallocation]*.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec::Vec;
    ///
    /// let mut vec = Vec::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// ```
    ///
    /// # Panics
    ///
    /// * if the requested capacity exceeds `usize::MAX` bytes.
    /// * on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    ///
    /// # Aborts
    ///
    /// * on OOM
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_in(capacity, Global)
    }

    /// Creates a `Vec<T>` directly from the raw components of another vector.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` needs to have been previously allocated via [`String`]/`Vec<T>`
    ///   (at least, it's highly likely to be incorrect if it wasn't).
    /// * `ptr`'s `T` needs to have the same size and alignment as it was allocated with.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length `size_t`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: liballoc::string::String
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    /// use std::ptr;
    /// use std::mem;
    ///
    /// let v = vec![1, 2, 3];
    // FIXME Update this when vec_into_raw_parts is stabilized
    /// // Prevent running `v`'s destructor so we are in complete control
    /// // of the allocation.
    /// let mut v = mem::ManuallyDrop::new(v);
    ///
    /// // Pull out the various important pieces of information about `v`
    /// let p = v.as_mut_ptr();
    /// let len = v.len();
    /// let cap = v.capacity();
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..len as isize {
    ///         ptr::write(p.offset(i), 4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let rebuilt = Vec::from_raw_parts(p, len, cap);
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    pub unsafe fn from_raw_parts(ptr: *mut T, length: usize, capacity: usize) -> Self {
        Self {
            buf: RawVec::from_raw_parts(ptr, capacity),
            len: length,
        }
    }
}

impl<T, A: DeallocRef> Vec<T, A> {
    /// Like `new` but parameterized over the choice of allocator for the returned `Vec`.
    #[inline]
    pub fn new_in(a: A) -> Self {
        Self {
            buf: RawVec::new_in(a),
            len: 0,
        }
    }

    /// Like `with_capacity` but parameterized over the choice of allocator for the returned
    /// `Vec`.
    ///
    /// # Panics
    ///
    /// * if the requested capacity exceeds `usize::MAX` bytes.
    /// * on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    #[inline]
    pub fn with_capacity_in(capacity: usize, a: A) -> Self
    where
        A: AllocRef,
    {
        Self {
            buf: RawVec::with_capacity_in(capacity, a),
            len: 0,
        }
    }

    /// Like `with_capacity` but parameterized over the choice of allocator for the returned
    /// `Vec`.
    ///
    /// # Errors
    ///
    /// * `CapacityOverflow` if the requested capacity exceeds `usize::MAX` bytes.
    /// * `CapacityOverflow` on 32-bit platforms if the requested capacity exceeds `isize::MAX` bytes.
    /// * `AllocError` on OOM
    #[inline]
    pub fn try_with_capacity_in(capacity: usize, a: A) -> Result<Self, CollectionAllocErr<A>>
    where
        A: AllocRef,
    {
        Ok(Self {
            buf: RawVec::try_with_capacity_in(capacity, a)?,
            len: 0,
        })
    }

    /// Like `from_raw_parts` but parameterized over the choice of allocator for the returned
    /// `Vec`.
    /// # Safety
    /// see `from_raw_parts`
    pub unsafe fn from_raw_parts_in(
        ptr: *mut T,
        length: usize,
        capacity: usize,
        b: A::BuildAlloc,
    ) -> Self {
        Self {
            buf: RawVec::from_raw_parts_in(ptr, capacity, b),
            len: length,
        }
    }

    /// Decomposes a `Vec<T>` into its raw components.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the vector (in elements), and the allocated capacity of the
    /// data (in elements). These are the same arguments in the same
    /// order as the arguments to [`from_raw_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `Vec`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `Vec` with the [`from_raw_parts`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_raw_parts`]: Vec::from_raw_parts()
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{vec, vec::Vec};
    ///
    /// let v: Vec<i32> = vec![-1, 0, 1];
    ///
    /// let (ptr, len, cap) = v.into_raw_parts();
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr as *mut u32;
    ///
    ///     Vec::from_raw_parts(ptr, len, cap)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    pub fn into_raw_parts(self) -> (*mut T, usize, usize) {
        let mut me = mem::ManuallyDrop::new(self);
        (me.as_mut_ptr(), me.len(), me.capacity())
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec::Vec;
    ///
    /// let vec: Vec<i32> = Vec::with_capacity(10);
    /// assert_eq!(vec.capacity(), 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn reserve(&mut self, additional: usize)
    where
        A: ReallocRef,
    {
        self.buf.reserve(self.len, additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `Vec<T>`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1];
    /// vec.reserve_exact(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn reserve_exact(&mut self, additional: usize)
    where
        A: ReallocRef,
    {
        self.buf.reserve_exact(self.len, additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `Vec<T>`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, collections::CollectionAllocErr, vec::Vec};
    ///
    /// fn process_data(data: &[u32]) -> Result<Vec<u32>, CollectionAllocErr<Global>> {
    ///     let mut output = Vec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.buf.try_reserve(self.len, additional)
    }

    /// Tries to reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `Vec<T>`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{alloc::Global, collections::CollectionAllocErr, vec::Vec};
    ///
    /// fn process_data(data: &[u32]) -> Result<Vec<u32>, CollectionAllocErr<Global>> {
    ///     let mut output = Vec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.buf.try_reserve_exact(self.len, additional)
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec::Vec;
    ///
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() >= 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn shrink_to_fit(&mut self)
    where
        A: ReallocRef,
    {
        if self.capacity() != self.len {
            self.buf.shrink_to_fit(self.len);
        }
    }

    /// Same as `shrink_to_fit` but returns errors instead of panicking.
    pub fn try_shrink_to_fit(&mut self) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        if self.capacity() != self.len {
            self.buf.try_shrink_to_fit(self.len)?;
        }
        Ok(())
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// Panics if the current capacity is smaller than the supplied
    /// minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec::Vec;
    ///
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to(4);
    /// assert!(vec.capacity() >= 4);
    /// vec.shrink_to(0);
    /// assert!(vec.capacity() >= 3);
    /// ```
    ///
    /// # Panics
    ///
    /// * Panics if the given amount is *larger* than the current capacity.
    /// * Panics if the reallocation fails.
    pub fn shrink_to(&mut self, min_capacity: usize)
    where
        A: ReallocRef,
    {
        self.buf.shrink_to_fit(cmp::max(self.len, min_capacity));
    }

    /// Same as `shrink_to` but returns errors instead of panicking.
    pub fn try_shrink_to(&mut self, min_capacity: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.buf.try_shrink_to_fit(cmp::max(self.len, min_capacity))
    }

    /// Converts the vector into [`Box<[T]>`][owned slice].
    ///
    /// Note that this will drop any excess capacity.
    ///
    /// [owned slice]: crate::boxed::Box
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use alloc_wg::vec;
    ///
    /// let v = vec![1, 2, 3];
    ///
    /// let slice = v.into_boxed_slice();
    /// ```
    ///
    /// Any excess capacity is removed:
    ///
    /// ```
    /// # // FIXME: alloc_wg Vec not possible as a slice converts to standard Vec
    /// let mut vec = Vec::with_capacity(10);
    /// vec.extend([1, 2, 3].iter().cloned());
    ///
    /// assert_eq!(vec.capacity(), 10);
    /// let slice = vec.into_boxed_slice();
    /// assert_eq!(slice.into_vec().capacity(), 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn into_boxed_slice(self) -> Box<[T], A>
    where
        A: ReallocRef,
    {
        match self.try_into_boxed_slice() {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `into_boxed_slice` but returns errors instead of panicking.
    pub fn try_into_boxed_slice(mut self) -> Result<Box<[T], A>, CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        unsafe {
            self.try_shrink_to_fit()?;
            let ptr = self.buf.ptr();
            let slice = slice::from_raw_parts_mut(ptr, self.buf.capacity());
            let builder = ptr::read(self.buf.build_alloc());
            let output = Box::from_raw_in(slice, builder);
            mem::forget(self);
            Ok(output)
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// The [`drain`] method can emulate `truncate`, but causes the excess
    /// elements to be returned instead of dropped.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// vec.truncate(2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(8);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// vec.truncate(0);
    /// assert_eq!(vec, []);
    /// ```
    ///
    /// [`clear`]: Vec::clear()
    /// [`drain`]: Vec::drain()
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len`
        //   case avoids creating an invalid slice, and
        // * the `len` of the vector is shrunk before calling `drop_in_place`,
        //   such that no value will be dropped twice in case `drop_in_place`
        //   were to panic once (if it panics twice, the program aborts).
        unsafe {
            if len > self.len {
                return;
            }
            #[allow(trivial_casts)]
            let s = self.get_unchecked_mut(len..) as *mut _;
            self.len = len;
            ptr::drop_in_place(s);
        }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// use std::io::{self, Write};
    /// let buffer = vec![1, 2, 3, 5, 8];
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// use std::io::{self, Read};
    /// let mut buffer = vec![0; 3];
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let x = vec![1, 2, 4];
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Vec::as_mut_ptr()
    #[inline]
    #[allow(clippy::let_and_return)]
    pub fn as_ptr(&self) -> *const T {
        // We shadow the slice method of the same name to avoid going through
        // `deref`, which creates an intermediate reference.
        let ptr = self.buf.ptr();
        unsafe { assume(!ptr.is_null()) };
        ptr
    }

    /// Returns an unsafe mutable pointer to the vector's buffer.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec::Vec;
    ///
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: Vec<i32> = Vec::with_capacity(size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as i32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&*x, &[0, 1, 2, 3]);
    /// ```
    #[inline]
    #[allow(clippy::let_and_return)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        // We shadow the slice method of the same name to avoid going through
        // `deref_mut`, which creates an intermediate reference.
        let ptr = self.buf.ptr();
        unsafe { assume(!ptr.is_null()) };
        ptr
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a vector
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: Vec::truncate()
    /// [`resize`]: Vec::resize()
    /// [`extend`]: #method.extend-1
    /// [`clear`]: Vec::clear()
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity`]: Vec::capacity()
    ///
    /// # Examples
    ///
    /// This method can be useful for situations in which the vector
    /// is serving as a buffer for other code, particularly over FFI:
    ///
    /// ```no_run
    /// # #![allow(dead_code)]
    /// use alloc_wg::vec::Vec;
    ///
    /// # // This is just a minimal skeleton for the doc example;
    /// # // don't use this as a starting point for a real library.
    /// # pub struct StreamWrapper { strm: *mut std::ffi::c_void }
    /// # const Z_OK: i32 = 0;
    /// # extern "C" {
    /// #     fn deflateGetDictionary(
    /// #         strm: *mut std::ffi::c_void,
    /// #         dictionary: *mut u8,
    /// #         dict_length: *mut usize,
    /// #     ) -> i32;
    /// # }
    /// # impl StreamWrapper {
    /// pub fn get_dictionary(&self) -> Option<Vec<u8>> {
    ///     // Per the FFI method's docs, "32768 bytes is always enough".
    ///     let mut dict = Vec::with_capacity(32_768);
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     // which makes `set_len` safe to call.
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized.
    ///             dict.set_len(dict_length);
    ///             Some(dict)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    ///
    /// While the following example is sound, there is a memory leak since
    /// the inner vectors were not freed prior to the `set_len` call:
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]];
    /// // SAFETY:
    /// // 1. `old_len..0` is empty so no elements need to be initialized.
    /// // 2. `0 <= capacity` always holds whatever `capacity` is.
    /// unsafe {
    ///     vec.set_len(0);
    /// }
    /// ```
    ///
    /// Normally, here, one would use [`clear`] instead to correctly drop
    /// the contents and thus not leak memory.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.len = new_len;
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut v = vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        unsafe {
            // We replace self[index] with the last element. Note that if the
            // bounds check on hole succeeds there must be a last element (which
            // can be self[index] itself).
            let hole: *mut T = &mut self[index];
            let last = ptr::read(self.get_unchecked(self.len - 1));
            self.len -= 1;
            ptr::replace(hole, last)
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// vec.insert(1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T)
    where
        A: ReallocRef,
    {
        match self.try_insert(index, element) {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `insert` but returns errors instead of panicking
    pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let len = self.len();
        assert!(index <= len);

        // space for the new element
        if len == self.buf.capacity() {
            self.try_reserve(1)?;
        }

        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().add(index);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }
        Ok(())
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut v = vec![1, 2, 3];
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, [1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len);
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().add(index);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec, [2, 4]);
    /// ```
    ///
    /// The exact order may be useful for tracking external state, like an index.
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3, 4, 5];
    /// let keep = [false, true, true, false, true];
    /// let mut i = 0;
    /// vec.retain(|_| (keep[i], i += 1).0);
    /// assert_eq!(vec, [2, 3, 5]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
        A: ReallocRef,
    {
        self.drain_filter(|x| !f(x));
    }

    /// Removes all but the first of consecutive elements in the vector that resolve to the same
    /// key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![10, 20, 21, 30, 20];
    ///
    /// vec.dedup_by_key(|i| *i / 10);
    ///
    /// assert_eq!(vec, [10, 20, 30, 20]);
    /// ```
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b))
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector and
    /// must determine if the elements compare equal. The elements are passed in opposite order
    /// from their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec!["foo", "bar", "Bar", "baz", "bar"];
    ///
    /// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(vec, ["foo", "bar", "baz", "bar"]);
    /// ```
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let len = {
            let (dedup, _) = partition_dedup_by(self.as_mut_slice(), same_bucket);
            dedup.len()
        };
        self.truncate(len);
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    #[inline]
    pub fn push(&mut self, value: T)
    where
        A: ReallocRef,
    {
        match self.try_push(value) {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    unsafe fn push_unchecked(&mut self, value: T)
    where
        A: AllocRef,
    {
        let len = self.len();
        debug_assert!(self.capacity() > len);
        ptr::write(self.get_unchecked_mut(len), value);
        // NB can't overflow since we would have had to alloc the address space
        self.set_len(len + 1);
    }

    /// Same as `push` but returns errors instead of panicking
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        // This will panic or abort if we would allocate > isize::MAX bytes
        // or if the length increment would overflow for zero-sized types.
        if self.len == self.buf.capacity() {
            self.try_reserve(1)?;
        }
        unsafe {
            self.push_unchecked(value);
        }
        Ok(())
    }

    /// Removes the last element from a vector and returns it, or [`None`][] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                Some(ptr::read(self.get_unchecked(self.len())))
            }
        }
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut vec = vec![1, 2, 3];
    /// let mut vec2 = vec![4, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2, []);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    #[inline]
    pub fn append(&mut self, other: &mut Self)
    where
        A: ReallocRef,
    {
        match self.try_append(other) {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `append` but returns errors instead of panicking.
    #[inline]
    pub fn try_append(&mut self, other: &mut Self) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        unsafe {
            self.try_append_elements(other.as_slice())?;
            other.set_len(0);
        }
        Ok(())
    }

    /// Appends elements to `Self` from other buffer.
    #[inline]
    unsafe fn try_append_elements(&mut self, other: *const [T]) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let count = (*other).len();
        self.try_reserve(count)?;
        let len = self.len();
        ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(len), count);
        self.len += count;
        Ok(())
    }

    /// Creates a draining iterator that removes the specified range in the vector
    /// and yields the removed items.
    ///
    /// Note 1: The element range is removed even if the iterator is only
    /// partially consumed or not consumed at all.
    ///
    /// Note 2: It is unspecified how many elements are removed from the vector
    /// if the `Drain` value is leaked.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::vec;
    ///
    /// let mut v = vec![1, 2, 3];
    /// let u: Vec<_> = v.drain(1..).collect();
    /// assert_eq!(v, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the vector
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // When the Drain is first created, it shortens the length of
        // the source vector to make sure no uninitialized or moved-from elements
        // are accessible at all if the Drain's destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, remaining tail of the vec is copied back to cover
        // the hole, and the vector length is restored to the new length.
        //
        let len = self.len();
        let start = match range.start_bound() {
            Included(&n) => n,
            Excluded(&n) => n + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&n) => n + 1,
            Excluded(&n) => n,
            Unbounded => len,
        };
        assert!(start <= end);
        assert!(end <= len);

        unsafe {
            // set self.vec length's to start, to be safe in case Drain is leaked
            self.set_len(start);
            // Use the borrow in the IterMut to indicate borrowing behavior of the
            // whole Drain iterator (like &mut T).
            let range_slice = slice::from_raw_parts_mut(self.as_mut_ptr().add(start), end - start);
            Drain {
                tail_start: end,
                tail_len: len - end,
                iter: range_slice.iter(),
                vec: NonNull::from(self),
            }
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut v = vec![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let a = vec![1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec::Vec;
    /// let mut v = Vec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated `Self`. `self` contains elements `[0, at)`,
    /// and the returned `Self` contains elements `[at, len)`.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec![1, 2, 3];
    /// let vec2 = vec.split_off(1);
    /// assert_eq!(vec, [1]);
    /// assert_eq!(vec2, [2, 3]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the allocation of split part fails.
    #[inline]
    pub fn split_off(&mut self, at: usize) -> Self
    where
        A: AllocRef,
    {
        match self.try_split_off(at) {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `split_off` but returns errors instead of panicking.
    #[inline]
    pub fn try_split_off(&mut self, at: usize) -> Result<Self, CollectionAllocErr<A>>
    where
        A: AllocRef,
    {
        assert!(at <= self.len(), "`at` out of bounds");

        let other_len = self.len - at;
        let mut other = Self::try_with_capacity_in(other_len, self.buf.alloc_ref().0)?;

        // Unsafely `set_len` and copy items to `other`.
        unsafe {
            self.set_len(at);
            other.set_len(other_len);

            ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), other.len());
        }
        Ok(other)
    }

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in the `Vec` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`resize`]. If you want
    /// to use the [`Default`] trait to generate values, you can pass
    /// [`Default::default()`] as the second argument.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.resize_with(5, Default::default);
    /// assert_eq!(vec, [1, 2, 3, 0, 0]);
    ///
    /// let mut vec = vec![];
    /// let mut p = 1;
    /// vec.resize_with(4, || {
    ///     p *= 2;
    ///     p
    /// });
    /// assert_eq!(vec, [2, 4, 8, 16]);
    /// ```
    ///
    /// [`resize`]: #method.resize
    /// [`Clone`]: ../../std/clone/trait.Clone.html
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
        A: ReallocRef,
    {
        match self.try_resize_with(new_len, f) {
            Ok(vec) => vec,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `resize_with` but returns errors instead of panicking.
    pub fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), CollectionAllocErr<A>>
    where
        F: FnMut() -> T,
        A: ReallocRef,
    {
        let len = self.len();
        if new_len > len {
            self.try_extend_with(new_len - len, ExtendFunc(f))?;
        } else {
            self.truncate(new_len);
        }
        Ok(())
    }

    /// Consumes and leaks the `Vec`, returning a mutable reference to the contents,
    /// `&'a mut [T]`. Note that the type `T` must outlive the chosen lifetime
    /// `'a`. If the type has only static references, or none at all, then this
    /// may be chosen to be `'static`.
    ///
    /// This function is similar to the `leak` function on `Box`.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak.
    ///
    /// # Examples
    ///
    /// Simple usage:
    ///
    /// ```
    /// # use alloc_wg::{vec, vec::Vec};
    /// let x = vec![1, 2, 3];
    /// let static_ref: &'static mut [usize] = Vec::leak(x);
    /// static_ref[0] += 1;
    /// assert_eq!(static_ref, &[2, 2, 3]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    #[inline]
    pub fn leak<'a>(vec: Self) -> &'a mut [T]
    where
        T: 'a, // Technically not needed, but kept to be explicit.
        A: ReallocRef,
    {
        Box::leak(vec.into_boxed_slice())
    }

    /// Same as `leak` but returns errors instead of panicking.
    #[inline]
    pub fn try_leak<'a>(vec: Self) -> Result<&'a mut [T], CollectionAllocErr<A>>
    where
        T: 'a, // Technically not needed, but kept to be explicit.
        A: ReallocRef,
    {
        Ok(Box::leak(vec.try_into_boxed_slice()?))
    }
}

impl<T: Clone, A: ReallocRef> Vec<T, A> {
    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method requires [`Clone`] to be able clone the passed value. If
    /// you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`resize_with`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec!["hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(vec, ["hello", "world", "world"]);
    ///
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.resize(2, 0);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// [`Clone`]: ../../std/clone/trait.Clone.html
    /// [`Default`]: ../../std/default/trait.Default.html
    /// [`resize_with`]: #method.resize_with
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn resize(&mut self, new_len: usize, value: T) {
        match self.try_resize(new_len, value) {
            Ok(_) => (),
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    /// Same as `resize` but returns errors instead of panicking
    pub fn try_resize(&mut self, new_len: usize, value: T) -> Result<(), CollectionAllocErr<A>> {
        let len = self.len();

        if new_len > len {
            self.try_extend_with(new_len - len, ExtendElement(value))?
        } else {
            self.truncate(new_len);
        }
        Ok(())
    }

    /// Clones and appends all elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `Vec`. The `other` vector is traversed in-order.
    ///
    /// Note that this function is same as [`extend`] except that it is
    /// specialized to work with slices instead. If and when Rust gets
    /// specialization this function will likely be deprecated (but still
    /// available).
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec![1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend`]: #method.extend
    ///
    /// # Panics
    ///
    /// Panics if the reallocation fails.
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.spec_extend(other.iter())
    }

    /// Same as `extend_from_slice` but returns errors instead of panicking
    pub fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), CollectionAllocErr<A>> {
        self.try_spec_extend(other.iter())
    }
}

// This code generalises `extend_with_{element,default}`.
trait ExtendWith<T> {
    fn next(&mut self) -> T;
    fn last(self) -> T;
}

struct ExtendElement<T>(T);
impl<T: Clone> ExtendWith<T> for ExtendElement<T> {
    fn next(&mut self) -> T {
        self.0.clone()
    }
    fn last(self) -> T {
        self.0
    }
}

struct ExtendDefault;
impl<T: Default> ExtendWith<T> for ExtendDefault {
    fn next(&mut self) -> T {
        Default::default()
    }
    fn last(self) -> T {
        Default::default()
    }
}

struct ExtendFunc<F>(F);
impl<T, F: FnMut() -> T> ExtendWith<T> for ExtendFunc<F> {
    fn next(&mut self) -> T {
        (self.0)()
    }
    fn last(mut self) -> T {
        (self.0)()
    }
}

impl<T, A: DeallocRef> Vec<T, A> {
    /// Same as `extend_with` but returns errors instead of panicking.
    fn try_extend_with<E: ExtendWith<T>>(
        &mut self,
        n: usize,
        mut value: E,
    ) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.try_reserve(n)?;

        unsafe {
            let mut ptr = self.as_mut_ptr().add(self.len());
            // Use SetLenOnDrop to work around bug where compiler
            // may not realize the store through `ptr` through self.set_len()
            // don't alias.
            let mut local_len = SetLenOnDrop::new(&mut self.len);

            // Write all elements except the last one
            for _ in 1..n {
                ptr::write(ptr, value.next());
                ptr = ptr.offset(1);
                // Increment the length in every step in case next() panics
                local_len.increment_len(1);
            }

            if n > 0 {
                // We can write the last element directly without cloning needlessly
                ptr::write(ptr, value.last());
                local_len.increment_len(1);
            }

            // len set by scope guard
        }
        Ok(())
    }
}

// Set the length of the vec when the `SetLenOnDrop` value goes out of scope.
//
// The idea is: The length field in SetLenOnDrop is a local variable
// that the optimizer will see does not alias with any stores through the Vec's data
// pointer. This is a workaround for alias analysis issue #32155
struct SetLenOnDrop<'a> {
    len: &'a mut usize,
    local_len: usize,
}

impl<'a> SetLenOnDrop<'a> {
    #[inline]
    fn new(len: &'a mut usize) -> Self {
        SetLenOnDrop {
            local_len: *len,
            len,
        }
    }

    #[inline]
    fn increment_len(&mut self, increment: usize) {
        self.local_len += increment;
    }
}

impl Drop for SetLenOnDrop<'_> {
    #[inline]
    fn drop(&mut self) {
        *self.len = self.local_len;
    }
}

impl<T: PartialEq, A: DeallocRef> Vec<T, A> {
    /// Removes consecutive repeated elements in the vector according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec![1, 2, 2, 3, 2];
    ///
    /// vec.dedup();
    ///
    /// assert_eq!(vec, [1, 2, 3, 2]);
    /// ```
    #[inline]
    pub fn dedup(&mut self) {
        self.dedup_by(|a, b| a == b)
    }

    /// Removes the first instance of `item` from the vector if the item exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec![1, 2, 3, 1];
    ///
    /// vec.remove_item(&1);
    ///
    /// assert_eq!(vec, vec![2, 3, 1]);
    /// ```
    pub fn remove_item(&mut self, item: &T) -> Option<T> {
        let pos = self.iter().position(|x| *x == *item)?;
        Some(self.remove(pos))
    }
}

////////////////////////////////////////////////////////////////////////////////
// Internal methods and functions
////////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
    from_elem_in(elem, n, Global)
}

#[doc(hidden)]
pub fn from_elem_in<T: Clone, A>(elem: T, n: usize, a: A) -> Vec<T, A>
where
    A: ReallocRef,
{
    match try_from_elem_in(elem, n, a) {
        Ok(vec) => vec,
        Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
        Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
    }
}

#[doc(hidden)]
pub fn try_from_elem_in<T: Clone, A: ReallocRef>(
    elem: T,
    n: usize,
    a: A,
) -> Result<Vec<T, A>, CollectionAllocErr<A>> {
    <T as SpecFromElem<A>>::try_from_elem_in(elem, n, a)
}

// Specialization trait used for Vec::from_elem
trait SpecFromElem<A: AllocRef>: Sized {
    fn try_from_elem_in(elem: Self, n: usize, a: A) -> Result<Vec<Self, A>, CollectionAllocErr<A>>;
}

impl<T: Clone, A: ReallocRef> SpecFromElem<A> for T {
    default fn try_from_elem_in(
        elem: Self,
        n: usize,
        a: A,
    ) -> Result<Vec<Self, A>, CollectionAllocErr<A>> {
        let mut v = Vec::try_with_capacity_in(n, a)?;
        v.try_extend_with(n, ExtendElement(elem))?;
        Ok(v)
    }
}

#[allow(clippy::use_self)]
impl<A: ReallocRef> SpecFromElem<A> for u8 {
    #[inline]
    fn try_from_elem_in(elem: Self, n: usize, a: A) -> Result<Vec<Self, A>, CollectionAllocErr<A>> {
        if elem == 0 {
            return Ok(Vec {
                buf: RawVec::try_with_capacity_zeroed_in(n, a)?,
                len: n,
            });
        }
        unsafe {
            let mut v = Vec::try_with_capacity_in(n, a)?;
            ptr::write_bytes(v.as_mut_ptr(), elem, n);
            v.set_len(n);
            Ok(v)
        }
    }
}

impl<T: Clone + IsZero, A: ReallocRef> SpecFromElem<A> for T {
    #[inline]
    fn try_from_elem_in(elem: Self, n: usize, a: A) -> Result<Vec<Self, A>, CollectionAllocErr<A>> {
        if elem.is_zero() {
            return Ok(Vec {
                buf: RawVec::try_with_capacity_zeroed_in(n, a)?,
                len: n,
            });
        }
        let mut v = Vec::try_with_capacity_in(n, a)?;
        v.try_extend_with(n, ExtendElement(elem))?;
        Ok(v)
    }
}

unsafe trait IsZero {
    /// Whether this value is zero
    fn is_zero(&self) -> bool;
}

macro_rules! impl_is_zero {
    ($t:ty, $is_zero:expr) => {
        unsafe impl IsZero for $t {
            #[inline]
            fn is_zero(&self) -> bool {
                $is_zero(*self)
            }
        }
    };
}

impl_is_zero!(i8, |x| x == 0);
impl_is_zero!(i16, |x| x == 0);
impl_is_zero!(i32, |x| x == 0);
impl_is_zero!(i64, |x| x == 0);
impl_is_zero!(i128, |x| x == 0);
impl_is_zero!(isize, |x| x == 0);

impl_is_zero!(u16, |x| x == 0);
impl_is_zero!(u32, |x| x == 0);
impl_is_zero!(u64, |x| x == 0);
impl_is_zero!(u128, |x| x == 0);
impl_is_zero!(usize, |x| x == 0);

impl_is_zero!(bool, |x: Self| !x);
impl_is_zero!(char, |x| x == '\0');

impl_is_zero!(f32, |x: Self| x.to_bits() == 0);
impl_is_zero!(f64, |x: Self| x.to_bits() == 0);

unsafe impl<T> IsZero for *const T {
    #[inline]
    fn is_zero(&self) -> bool {
        (*self).is_null()
    }
}

unsafe impl<T> IsZero for *mut T {
    #[inline]
    fn is_zero(&self) -> bool {
        (*self).is_null()
    }
}

// `Option<&T>`, `Option<&mut T>` and `Option<Box<T>>` are guaranteed to represent `None` as null.
// For fat pointers, the bytes that would be the pointer metadata in the `Some` variant
// are padding in the `None` variant, so ignoring them and zero-initializing instead is ok.

unsafe impl<T: ?Sized> IsZero for Option<&T> {
    #[inline]
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

unsafe impl<T: ?Sized> IsZero for Option<&mut T> {
    #[inline]
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

unsafe impl<T: ?Sized> IsZero for Option<Box<T>> {
    #[inline]
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

////////////////////////////////////////////////////////////////////////////////
// Common trait implementations for Vec
////////////////////////////////////////////////////////////////////////////////

impl<T: Clone, A> Clone for Vec<T, A>
where
    A: AllocRef,
    A::BuildAlloc: Clone,
{
    #[must_use]
    #[inline]
    fn clone(&self) -> Self {
        let mut b = self.buf.build_alloc().clone();
        let old_layout = self.buf.current_layout();

        unsafe {
            let old_ptr = NonNull::new_unchecked(self.buf.ptr());
            let a = b.build_alloc_ref(old_ptr.cast(), old_layout);
            self.clone_in(a)
        }
    }
}

#[allow(clippy::use_self)]
impl<T: Clone, A: AllocRef, B: AllocRef> CloneIn<B> for Vec<T, A> {
    type Cloned = Vec<T, B>;

    fn clone_in(&self, a: B) -> Self::Cloned {
        let mut v = Vec::with_capacity_in(self.len(), a);

        self.iter()
            .cloned()
            .for_each(|element| unsafe { v.push_unchecked(element) });
        v
    }

    fn try_clone_in(&self, a: B) -> Result<Self::Cloned, B::Error> {
        let mut v = Vec::try_with_capacity_in(self.len(), a).map_err(|e| match e {
            CollectionAllocErr::CapacityOverflow => unreachable!("capacity overflow in clone"),
            CollectionAllocErr::AllocError { inner, .. } => inner,
        })?;

        self.iter()
            .cloned()
            .for_each(|element| unsafe { v.push_unchecked(element) });
        Ok(v)
    }
}

impl<T: Hash, A: DeallocRef> Hash for Vec<T, A> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T, A: DeallocRef, I: SliceIndex<[T]>> Index<I> for Vec<T, A> {
    type Output = I::Output;

    #[inline]
    #[must_use]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(&**self, index)
    }
}

impl<T, A: DeallocRef, I: SliceIndex<[T]>> IndexMut<I> for Vec<T, A> {
    #[inline]
    #[must_use]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl<T, A: DeallocRef> ops::Deref for Vec<T, A> {
    type Target = [T];

    #[must_use]
    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }
}

impl<T, A: DeallocRef> ops::DerefMut for Vec<T, A> {
    #[must_use]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }
}

impl<T> FromIterator<T> for Vec<T> {
    #[inline]
    #[must_use]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        <Self as SpecExtend<T, I::IntoIter, Global>>::from_iter_in(iter.into_iter(), Global)
    }
}

impl<T, A: ReallocRef> FromIteratorIn<T, A> for Vec<T, A> {
    #[inline]
    #[must_use]
    fn from_iter_in<I: IntoIterator<Item = T>>(iter: I, a: A) -> Self {
        <Self as SpecExtend<T, I::IntoIter, A>>::from_iter_in(iter.into_iter(), a)
    }

    #[inline]
    fn try_from_iter_in<I: IntoIterator<Item = T>>(
        iter: I,
        a: A,
    ) -> Result<Self, CollectionAllocErr<A>> {
        <Self as SpecExtend<T, I::IntoIter, A>>::try_from_iter_in(iter.into_iter(), a)
    }
}

impl<T, A: DeallocRef> IntoIterator for Vec<T, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the vector (from start to end). The vector cannot be used after calling
    /// this.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let v = vec!["a".to_string(), "b".to_string()];
    /// for s in v.into_iter() {
    ///     // s has type String, not &String
    ///     println!("{}", s);
    /// }
    /// ```
    #[inline]
    #[must_use]
    #[allow(clippy::cast_possible_wrap)]
    fn into_iter(mut self) -> IntoIter<T, A> {
        unsafe {
            let begin = self.as_mut_ptr();
            let end = if mem::size_of::<T>() == 0 {
                arith_offset(begin as *const i8, self.len() as isize) as *const T
            } else {
                begin.add(self.len())
            };
            let cap = self.buf.capacity();
            let build_alloc = ptr::read(self.buf.build_alloc_mut());
            mem::forget(self);
            IntoIter {
                buf: RawVec::from_raw_parts_in(begin, cap, build_alloc),
                ptr: begin,
                end,
            }
        }
    }
}

impl<'a, T, A: DeallocRef> IntoIterator for &'a Vec<T, A> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[must_use]
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T, A: DeallocRef> IntoIterator for &'a mut Vec<T, A> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T, A> Extend<T> for Vec<T, A>
where
    A: ReallocRef,
{
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<T, I::IntoIter, A>>::spec_extend(self, iter.into_iter())
    }
}

impl<T, A: ReallocRef> TryExtend<T> for Vec<T, A> {
    type Err = CollectionAllocErr<A>;

    #[inline]
    fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), Self::Err> {
        <Self as SpecExtend<T, I::IntoIter, A>>::try_spec_extend(self, iter.into_iter())
    }
}

trait SpecExtend<T, I, A: AllocRef>: Sized {
    #[inline]
    fn from_iter_in(iter: I, a: A) -> Self {
        match Self::try_from_iter_in(iter, a) {
            Ok(v) => v,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    fn try_from_iter_in(iter: I, a: A) -> Result<Self, CollectionAllocErr<A>>;

    #[inline]
    fn spec_extend(&mut self, iter: I) {
        match self.try_spec_extend(iter) {
            Ok(_) => (),
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { layout, .. }) => handle_alloc_error(layout.into()),
        }
    }

    fn try_spec_extend(&mut self, iter: I) -> Result<(), CollectionAllocErr<A>>;
}

impl<T, I, A> SpecExtend<T, I, A> for Vec<T, A>
where
    I: Iterator<Item = T>,
    A: ReallocRef,
{
    default fn try_from_iter_in(mut iter: I, a: A) -> Result<Self, CollectionAllocErr<A>> {
        // Unroll the first iteration, as the vector is going to be
        // expanded on this iteration in every case when the iterable is not
        // empty, but the loop in extend_desugared() is not going to see the
        // vector being full in the few subsequent loop iterations.
        // So we get better branch prediction.
        let mut vector = match iter.next() {
            None => return Ok(Self::new_in(a)),
            Some(element) => {
                let (lower, _) = iter.size_hint();
                let mut vector = Self::try_with_capacity_in(lower.saturating_add(1), a)?;
                unsafe {
                    ptr::write(vector.get_unchecked_mut(0), element);
                    vector.set_len(1);
                }
                vector
            }
        };
        vector.try_spec_extend(iter)?;
        Ok(vector)
    }

    default fn try_spec_extend(&mut self, iter: I) -> Result<(), CollectionAllocErr<A>> {
        self.try_extend_desugared(iter)
    }
}

impl<T, I, A: ReallocRef> SpecExtend<T, I, A> for Vec<T, A>
where
    I: TrustedLen<Item = T>,
{
    default fn try_from_iter_in(iter: I, a: A) -> Result<Self, CollectionAllocErr<A>> {
        let mut vector = Self::new_in(a);
        vector.try_spec_extend(iter)?;
        Ok(vector)
    }

    default fn try_spec_extend(&mut self, iter: I) -> Result<(), CollectionAllocErr<A>> {
        // This is the case for a TrustedLen iterator.
        let (low, high) = iter.size_hint();
        if let Some(high_value) = high {
            debug_assert_eq!(
                low,
                high_value,
                "TrustedLen iterator's size hint is not exact: {:?}",
                (low, high)
            );
        }
        if let Some(additional) = high {
            self.try_reserve(additional)?;
            unsafe {
                let mut ptr = self.as_mut_ptr().add(self.len());
                let mut local_len = SetLenOnDrop::new(&mut self.len);
                iter.for_each(move |element| {
                    ptr::write(ptr, element);
                    ptr = ptr.offset(1);
                    // NB can't overflow since we would have had to alloc the address space
                    local_len.increment_len(1);
                });
            }
        } else {
            self.try_extend_desugared(iter)?
        }
        Ok(())
    }
}

impl<T, A: ReallocRef> SpecExtend<T, IntoIter<T, A>, A> for Vec<T, A> {
    fn try_from_iter_in(iter: IntoIter<T, A>, mut a: A) -> Result<Self, CollectionAllocErr<A>> {
        // A common case is passing a vector into a function which immediately
        // re-collects into a vector. We can short circuit this if the IntoIter
        // has not been advanced at all.
        let ptr: *const T = iter.buf.ptr();
        if ptr == iter.ptr {
            unsafe {
                let vec = Self::from_raw_parts_in(
                    iter.buf.ptr(),
                    iter.len(),
                    iter.buf.capacity(),
                    a.get_build_alloc(),
                );
                mem::forget(iter);
                Ok(vec)
            }
        } else {
            let mut vector = Self::new_in(a);
            vector.try_spec_extend(iter)?;
            Ok(vector)
        }
    }

    fn try_spec_extend(&mut self, mut iter: IntoIter<T, A>) -> Result<(), CollectionAllocErr<A>> {
        unsafe {
            self.try_append_elements(iter.as_slice())?;
        }
        iter.ptr = iter.end;
        Ok(())
    }
}

impl<'a, T: 'a, I, A: ReallocRef> SpecExtend<&'a T, I, A> for Vec<T, A>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    default fn try_from_iter_in(iterator: I, a: A) -> Result<Self, CollectionAllocErr<A>> {
        SpecExtend::try_from_iter_in(iterator.cloned(), a)
    }

    default fn try_spec_extend(&mut self, iterator: I) -> Result<(), CollectionAllocErr<A>> {
        self.try_spec_extend(iterator.cloned())
    }
}

impl<'a, T: 'a, A: ReallocRef> SpecExtend<&'a T, slice::Iter<'a, T>, A> for Vec<T, A>
where
    T: Copy,
{
    fn try_spec_extend(&mut self, iter: slice::Iter<'a, T>) -> Result<(), CollectionAllocErr<A>> {
        let slice = iter.as_slice();
        self.try_reserve(slice.len())?;
        unsafe {
            let len = self.len();
            self.set_len(len + slice.len());
            self.get_unchecked_mut(len..).copy_from_slice(slice);
        }
        Ok(())
    }
}

impl<T, A: DeallocRef> Vec<T, A> {
    fn try_extend_desugared<I: Iterator<Item = T>>(
        &mut self,
        mut iterator: I,
    ) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        // This is the case for a general iterator.
        //
        // This function should be the moral equivalent of:
        //
        //      for item in iterator {
        //          self.push(item);
        //      }
        while let Some(element) = iterator.next() {
            let len = self.len();
            if len == self.capacity() {
                let (lower, _) = iterator.size_hint();
                self.try_reserve(lower.saturating_add(1))?;
            }
            unsafe {
                self.push_unchecked(element);
            }
        }
        Ok(())
    }

    /// Creates a splicing iterator that replaces the specified range in the vector
    /// with the given `replace_with` iterator and yields the removed items.
    /// `replace_with` does not need to be the same length as `range`.
    ///
    /// The element range is removed even if the iterator is not consumed until the end.
    ///
    /// It is unspecified how many elements are removed from the vector
    /// if the `Splice` value is leaked.
    ///
    /// The input iterator `replace_with` is only consumed when the `Splice` value is dropped.
    ///
    /// This is optimal if:
    ///
    /// * The tail (elements in the vector after `range`) is empty,
    /// * or `replace_with` yields fewer elements than `range`’s length
    /// * or the lower bound of its `size_hint()` is exact.
    ///
    /// Otherwise, a temporary vector is allocated and the tail is moved twice.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut v = vec![1, 2, 3];
    /// let new = [7, 8];
    /// let u: Vec<_> = v.splice(..2, new.iter().cloned()).collect();
    /// assert_eq!(v, &[7, 8, 3]);
    /// assert_eq!(u, &[1, 2]);
    /// ```
    #[inline]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter, A>
    where
        A: ReallocRef,
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
    {
        Splice {
            drain: self.drain(range),
            replace_with: replace_with.into_iter(),
        }
    }

    /// Creates an iterator which uses a closure to determine if an element should be removed.
    ///
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the vector and will not be yielded
    /// by the iterator.
    ///
    /// Using this method is equivalent to the following code:
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use alloc_wg::vec;
    /// # let some_predicate = |x: &mut i32| { *x == 2 || *x == 3 || *x == 6 };
    /// # let mut vec = vec![1, 2, 3, 4, 5, 6];
    /// let mut i = 0;
    /// while i != vec.len() {
    ///     if some_predicate(&mut vec[i]) {
    ///         let val = vec.remove(i);
    ///     // your code here
    ///     } else {
    ///         i += 1;
    ///     }
    /// }
    ///
    /// # assert_eq!(vec, vec![1, 4, 5]);
    /// ```
    ///
    /// But `drain_filter` is easier to use. `drain_filter` is also more efficient,
    /// because it can backshift the elements of the array in bulk.
    ///
    /// Note that `drain_filter` also lets you mutate every element in the filter closure,
    /// regardless of whether you choose to keep or remove it.
    ///
    ///
    /// # Examples
    ///
    /// Splitting an array into evens and odds, reusing the original allocation:
    ///
    /// ```
    /// # use alloc_wg::{vec, vec::Vec};
    /// let mut numbers = vec![1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15];
    ///
    /// let evens = numbers.drain_filter(|x| *x % 2 == 0).collect::<Vec<_>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(evens, vec![2, 4, 6, 8, 14]);
    /// assert_eq!(odds, vec![1, 3, 5, 9, 11, 13, 15]);
    /// ```
    pub fn drain_filter<F>(&mut self, filter: F) -> DrainFilter<'_, T, F, A>
    where
        A: ReallocRef,
        F: FnMut(&mut T) -> bool,
    {
        let old_len = self.len();

        // Guard against us getting leaked (leak amplification)
        unsafe {
            self.set_len(0);
        }

        DrainFilter {
            vec: self,
            idx: 0,
            del: 0,
            old_len,
            pred: filter,
            panic_flag: false,
        }
    }
}

/// Extend implementation that copies elements out of references before pushing them onto the Vec.
///
/// This implementation is specialized for slice iterators, where it uses [`copy_from_slice`] to
/// append the entire slice at once.
///
/// [`copy_from_slice`]: ../../std/primitive.slice.html#method.copy_from_slice
impl<'a, T: 'a + Copy, A> Extend<&'a T> for Vec<T, A>
where
    A: ReallocRef,
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned())
    }
}

impl<'a, T: 'a + Copy, A> TryExtend<&'a T> for Vec<T, A>
where
    A: ReallocRef,
{
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) -> Result<(), Self::Err> {
        self.try_extend(iter.into_iter().cloned())
    }
}

macro_rules! __impl_slice_eq1 {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty, $($constraints:tt)*) => {
        impl<T, U, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
            $($constraints)*
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
            #[inline]
            #[allow(clippy::partialeq_ne_impl)]
            fn ne(&self, other: &$rhs) -> bool { self[..] != other[..] }
        }
    }
}

__impl_slice_eq1! { [A, B] Vec<T, A>, Vec<U, B>, A: DeallocRef, B: DeallocRef }
__impl_slice_eq1! { [A] Vec<T, A>, &[U], A: DeallocRef }
__impl_slice_eq1! { [A] Vec<T, A>, &mut [U], A: DeallocRef }
// __impl_slice_eq1! { [] Cow<'_, [A]>, &[B], A: Clone }
// __impl_slice_eq1! { [] Cow<'_, [A]>, &mut [B], A: Clone }
// __impl_slice_eq1! { [] Cow<'_, [A]>, Vec<B>, A: Clone }
__impl_slice_eq1! { [A, const N: usize] Vec<T, A>, [U; N], [U; N]: core::array::LengthAtMost32, A: DeallocRef }
__impl_slice_eq1! { [A, const N: usize] Vec<T, A>, &[U; N], [U; N]: core::array::LengthAtMost32, A: DeallocRef }

// NOTE: some less important impls are omitted to reduce code bloat
// FIXME(Centril): Reconsider this?
//__impl_slice_eq1! { [const N: usize] Vec<A>, &mut [B; N], [B; N]: LengthAtMost32 }
//__impl_slice_eq1! { [const N: usize] Cow<'a, [A]>, [B; N], [B; N]: LengthAtMost32 }
//__impl_slice_eq1! { [const N: usize] Cow<'a, [A]>, &[B; N], [B; N]: LengthAtMost32 }
//__impl_slice_eq1! { [const N: usize] Cow<'a, [A]>, &mut [B; N], [B; N]: LengthAtMost32 }

/// Implements comparison of vectors, lexicographically.
impl<T: PartialOrd, A: DeallocRef, B: DeallocRef> PartialOrd<Vec<T, B>> for Vec<T, A> {
    #[inline]
    #[must_use]
    fn partial_cmp(&self, other: &Vec<T, B>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Eq, A: DeallocRef> Eq for Vec<T, A> {}

/// Implements ordering of vectors, lexicographically.
impl<T: Ord, A: DeallocRef> Ord for Vec<T, A> {
    #[inline]
    #[must_use]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

unsafe impl<#[may_dangle] T, A: DeallocRef> Drop for Vec<T, A> {
    fn drop(&mut self) {
        unsafe {
            // use drop for [T]
            ptr::drop_in_place(&mut self[..]);
        }
        // RawVec handles deallocation
    }
}

impl<T, A: DeallocRef> Default for Vec<T, A>
where
    A: Default,
{
    /// Creates an empty `Vec<T>`.
    #[must_use]
    fn default() -> Self {
        Self::new_in(A::default())
    }
}

impl<T: fmt::Debug, A: DeallocRef> fmt::Debug for Vec<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T, A: DeallocRef> AsRef<Vec<T, A>> for Vec<T, A> {
    #[must_use]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, A: DeallocRef> AsMut<Vec<T, A>> for Vec<T, A> {
    #[must_use]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T, A: DeallocRef> AsRef<[T]> for Vec<T, A> {
    #[must_use]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, A: DeallocRef> AsMut<[T]> for Vec<T, A> {
    #[must_use]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: Clone> From<&[T]> for Vec<T> {
    #[must_use]
    fn from(s: &[T]) -> Self {
        let mut v = Self::new();
        v.extend(s.iter().cloned());
        v
    }
}

impl<T: Clone> From<&mut [T]> for Vec<T> {
    #[must_use]
    fn from(s: &mut [T]) -> Self {
        From::<&[T]>::from(s)
    }
}

// impl<'a, T> From<Cow<'a, [T]>> for Vec<T>
// where
//     [T]: ToOwned<Owned = Vec<T>>,
// {
//     #[must_use]
//     fn from(s: Cow<'a, [T]>) -> Self {
//         s.into_owned()
//     }
// }

// note: test pulls in libstd, which causes errors here
// #[cfg(not(test))]
// impl<T> From<Box<[T]>> for Vec<T> {
//     #[must_use]
//     fn from(s: Box<[T]>) -> Self {
//         s.into_vec()
//     }
// }

// note: test pulls in libstd, which causes errors here
#[cfg(not(test))]
impl<T> From<Vec<T>> for Box<[T]> {
    #[must_use]
    fn from(v: Vec<T>) -> Self {
        v.into_boxed_slice()
    }
}

impl From<&str> for Vec<u8> {
    #[must_use]
    fn from(s: &str) -> Self {
        From::from(s.as_bytes())
    }
}

////////////////////////////////////////////////////////////////////////////////
// Clone-on-write
////////////////////////////////////////////////////////////////////////////////

// impl<'a, T: Clone> From<&'a [T]> for Cow<'a, [T]> {
//     fn from(s: &'a [T]) -> Cow<'a, [T]> {
//         Cow::Borrowed(s)
//     }
// }

// impl<'a, T: Clone> From<Vec<T>> for Cow<'a, [T]> {
//     fn from(v: Vec<T>) -> Cow<'a, [T]> {
//         Cow::Owned(v)
//     }
// }

// impl<'a, T: Clone> From<&'a Vec<T>> for Cow<'a, [T]> {
//     fn from(v: &'a Vec<T>) -> Cow<'a, [T]> {
//         Cow::Borrowed(v.as_slice())
//     }
// }

// impl<'a, T> FromIterator<T> for Cow<'a, [T]>
// where
//     T: Clone,
// {
//     fn from_iter<I: IntoIterator<Item = T>>(it: I) -> Cow<'a, [T]> {
//         Cow::Owned(FromIterator::from_iter(it))
//     }
// }

////////////////////////////////////////////////////////////////////////////////
// Iterators
////////////////////////////////////////////////////////////////////////////////

/// An iterator that moves out of a vector.
///
/// This `struct` is created by the `into_iter` method on [`Vec`][`Vec`] (provided
/// by the [`IntoIterator`] trait).
///
/// [`Vec`]: struct.Vec.html
/// [`IntoIterator`]: ../../std/iter/trait.IntoIterator.html
pub struct IntoIter<T, A: DeallocRef = Global> {
    buf: RawVec<T, A>,
    ptr: *const T,
    end: *const T,
}

impl<T: fmt::Debug, A: DeallocRef> fmt::Debug for IntoIter<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
    }
}

impl<T, A: DeallocRef> IntoIter<T, A> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// let _ = into_iter.next().unwrap();
    /// assert_eq!(into_iter.as_slice(), &['b', 'c']);
    /// ```
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr, self.len()) }
    }

    /// Returns the remaining items of this iterator as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let vec = vec!['a', 'b', 'c'];
    /// let mut into_iter = vec.into_iter();
    /// assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
    /// into_iter.as_mut_slice()[2] = 'z';
    /// assert_eq!(into_iter.next().unwrap(), 'a');
    /// assert_eq!(into_iter.next().unwrap(), 'b');
    /// assert_eq!(into_iter.next().unwrap(), 'z');
    /// ```
    #[must_use]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr as *mut T, self.len()) }
    }
}

unsafe impl<T: Send, A: Send + DeallocRef> Send for IntoIter<T, A> {}
unsafe impl<T: Sync, A: Send + DeallocRef> Sync for IntoIter<T, A> {}

impl<T, A: DeallocRef> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        unsafe {
            if self.ptr == self.end {
                None
            } else if mem::size_of::<T>() == 0 {
                // purposefully don't use 'ptr.offset' because for
                // vectors with 0-size elements this would return the
                // same pointer.
                self.ptr = arith_offset(self.ptr as *const i8, 1) as *mut T;

                // Make up a value of this ZST.
                Some(mem::zeroed())
            } else {
                let old = self.ptr;
                self.ptr = self.ptr.offset(1);

                Some(ptr::read(old))
            }
        }
    }

    #[inline]
    #[must_use]
    #[allow(clippy::cast_sign_loss)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = if mem::size_of::<T>() == 0 {
            (self.end as usize).wrapping_sub(self.ptr as usize)
        } else {
            unsafe { offset_from(self.end, self.ptr) as usize }
        };
        (exact, Some(exact))
    }

    #[inline]
    #[must_use]
    fn count(self) -> usize {
        self.len()
    }
}

impl<T, A: DeallocRef> DoubleEndedIterator for IntoIter<T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        unsafe {
            if self.end == self.ptr {
                None
            } else if mem::size_of::<T>() == 0 {
                // See above for why 'ptr.offset' isn't used
                self.end = arith_offset(self.end as *const i8, -1) as *mut T;

                // Make up a value of this ZST.
                Some(mem::zeroed())
            } else {
                self.end = self.end.offset(-1);

                Some(ptr::read(self.end))
            }
        }
    }
}

impl<T, A: DeallocRef> ExactSizeIterator for IntoIter<T, A> {}

impl<T, A: DeallocRef> FusedIterator for IntoIter<T, A> {}

impl<T: Clone> Clone for IntoIter<T> {
    #[must_use]
    fn clone(&self) -> Self {
        let mut v = Vec::new();
        v.extend(self.as_slice().iter().cloned());
        v.into_iter()
    }
}

impl<T, A: DeallocRef> Drop for IntoIter<T, A> {
    fn drop(&mut self) {
        // destroy the remaining elements
        for _x in self.by_ref() {}

        // RawVec handles deallocation
    }
}

/// A draining iterator for `Vec<T>`.
///
/// This `struct` is created by the [`drain`] method on [`Vec`].
///
/// [`drain`]: struct.Vec.html#method.drain
/// [`Vec`]: struct.Vec.html
pub struct Drain<'a, T, A: DeallocRef = Global> {
    /// Index of tail to preserve
    tail_start: usize,
    /// Length of tail
    tail_len: usize,
    /// Current remaining range to remove
    iter: slice::Iter<'a, T>,
    vec: NonNull<Vec<T, A>>,
}

impl<T: fmt::Debug, A: DeallocRef> fmt::Debug for Drain<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.iter.as_slice()).finish()
    }
}

impl<T, A: DeallocRef> Drain<'_, T, A> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::vec;
    /// let mut vec = vec!['a', 'b', 'c'];
    /// let mut drain = vec.drain(..);
    /// assert_eq!(drain.as_slice(), &['a', 'b', 'c']);
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_slice(), &['b', 'c']);
    /// ```
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        self.iter.as_slice()
    }
}

unsafe impl<T: Sync, A: DeallocRef> Sync for Drain<'_, T, A> {}
unsafe impl<T: Send, A: DeallocRef> Send for Drain<'_, T, A> {}

impl<T, A: DeallocRef> Iterator for Drain<'_, T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|elt| unsafe { ptr::read(elt) })
    }

    #[must_use]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, A: DeallocRef> DoubleEndedIterator for Drain<'_, T, A> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|elt| unsafe { ptr::read(elt) })
    }
}

impl<T, A: DeallocRef> Drop for Drain<'_, T, A> {
    fn drop(&mut self) {
        // exhaust self first
        self.for_each(drop);

        if self.tail_len > 0 {
            unsafe {
                let source_vec = self.vec.as_mut();
                // memmove back untouched tail, update to new length
                let start = source_vec.len();
                let tail = self.tail_start;
                if tail != start {
                    let src = source_vec.as_ptr().add(tail);
                    let dst = source_vec.as_mut_ptr().add(start);
                    ptr::copy(src, dst, self.tail_len);
                }
                source_vec.set_len(start + self.tail_len);
            }
        }
    }
}

impl<T, A: DeallocRef> ExactSizeIterator for Drain<'_, T, A> {}

impl<T, A: DeallocRef> FusedIterator for Drain<'_, T, A> {}

/// A splicing iterator for `Vec`.
///
/// This struct is created by the [`splice()`] method on [`Vec`]. See its
/// documentation for more.
///
/// [`splice()`]: struct.Vec.html#method.splice
/// [`Vec`]: struct.Vec.html
#[derive(Debug)]
pub struct Splice<'a, I: Iterator + 'a, A = Global>
where
    A: ReallocRef,
{
    drain: Drain<'a, I::Item, A>,
    replace_with: I,
}

impl<I: Iterator, A> Iterator for Splice<'_, I, A>
where
    A: ReallocRef,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.drain.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.drain.size_hint()
    }
}

impl<I: Iterator, A> DoubleEndedIterator for Splice<'_, I, A>
where
    A: ReallocRef,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.drain.next_back()
    }
}

impl<I: Iterator, A> ExactSizeIterator for Splice<'_, I, A> where A: ReallocRef {}

impl<I: Iterator, A> Drop for Splice<'_, I, A>
where
    A: ReallocRef,
{
    fn drop(&mut self) {
        self.drain.by_ref().for_each(drop);

        unsafe {
            if self.drain.tail_len == 0 {
                self.drain.vec.as_mut().extend(self.replace_with.by_ref());
                return;
            }

            // First fill the range left by drain().
            if !self.drain.fill(&mut self.replace_with) {
                return;
            }

            // There may be more elements. Use the lower bound as an estimate.
            // FIXME: Is the upper bound a better guess? Or something else?
            let (lower_bound, _upper_bound) = self.replace_with.size_hint();
            if lower_bound > 0 {
                self.drain.move_tail(lower_bound);
                if !self.drain.fill(&mut self.replace_with) {
                    return;
                }
            }

            // Collect any remaining elements.
            // This is a zero-length vector which does not allocate if `lower_bound` was exact.
            let mut collected = Vec::new();
            collected.extend(self.replace_with.by_ref());
            let mut collected = collected.into_iter();
            // Now we have an exact count.
            if collected.len() > 0 {
                self.drain.move_tail(collected.len());
                let filled = self.drain.fill(&mut collected);
                debug_assert!(filled);
                debug_assert_eq!(collected.len(), 0);
            }
        }
        // Let `Drain::drop` move the tail back if necessary and restore `vec.len`.
    }
}

/// Private helper methods for `Splice::drop`
impl<T, A: DeallocRef> Drain<'_, T, A>
where
    A: ReallocRef,
{
    /// The range from `self.vec.len` to `self.tail_start` contains elements
    /// that have been moved out.
    /// Fill that range as much as possible with new elements from the `replace_with` iterator.
    /// Returns `true` if we filled the entire range. (`replace_with.next()` didn’t return `None`.)
    unsafe fn fill<I: Iterator<Item = T>>(&mut self, replace_with: &mut I) -> bool {
        let vec = self.vec.as_mut();
        let range_start = vec.len;
        let range_end = self.tail_start;
        let range_slice =
            slice::from_raw_parts_mut(vec.as_mut_ptr().add(range_start), range_end - range_start);

        for place in range_slice {
            if let Some(new_item) = replace_with.next() {
                ptr::write(place, new_item);
                vec.len += 1;
            } else {
                return false;
            }
        }
        true
    }

    /// Makes room for inserting more elements before the tail.
    unsafe fn move_tail(&mut self, extra_capacity: usize) {
        let vec = self.vec.as_mut();
        let used_capacity = self.tail_start + self.tail_len;
        vec.buf.reserve(used_capacity, extra_capacity);

        let new_tail_start = self.tail_start + extra_capacity;
        let src = vec.as_ptr().add(self.tail_start);
        let dst = vec.as_mut_ptr().add(new_tail_start);
        ptr::copy(src, dst, self.tail_len);
        self.tail_start = new_tail_start;
    }
}

/// An iterator produced by calling `drain_filter` on Vec.
// #[derive(Debug)]
pub struct DrainFilter<'a, T, F, A: DeallocRef = Global>
where
    F: FnMut(&mut T) -> bool,
{
    vec: &'a mut Vec<T, A>,
    /// The index of the item that will be inspected by the next call to `next`.
    idx: usize,
    /// The number of items that have been drained (removed) thus far.
    del: usize,
    /// The original length of `vec` prior to draining.
    old_len: usize,
    /// The filter test predicate.
    pred: F,
    /// A flag that indicates a panic has occured in the filter test prodicate.
    /// This is used as a hint in the drop implmentation to prevent consumption
    /// of the remainder of the `DrainFilter`. Any unprocessed items will be
    /// backshifted in the `vec`, but no further items will be dropped or
    /// tested by the filter predicate.
    panic_flag: bool,
}

impl<T, F, A: DeallocRef> Iterator for DrainFilter<'_, T, F, A>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        unsafe {
            while self.idx < self.old_len {
                let i = self.idx;
                let v = slice::from_raw_parts_mut(self.vec.as_mut_ptr(), self.old_len);
                self.panic_flag = true;
                let drained = (self.pred)(&mut v[i]);
                self.panic_flag = false;
                // Update the index *after* the predicate is called. If the index
                // is updated prior and the predicate panics, the element at this
                // index would be leaked.
                self.idx += 1;
                if drained {
                    self.del += 1;
                    return Some(ptr::read(&v[i]));
                } else if self.del > 0 {
                    let del = self.del;
                    let src: *const T = &v[i];
                    let dst: *mut T = &mut v[i - del];
                    ptr::copy_nonoverlapping(src, dst, 1);
                }
            }
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.idx))
    }
}

impl<T, F, A: DeallocRef> Drop for DrainFilter<'_, T, F, A>
where
    F: FnMut(&mut T) -> bool,
{
    fn drop(&mut self) {
        struct BackshiftOnDrop<'a, 'b, T, F, A: DeallocRef = Global>
        where
            F: FnMut(&mut T) -> bool,
        {
            drain: &'b mut DrainFilter<'a, T, F, A>,
        }

        impl<T, F, A: DeallocRef> Drop for BackshiftOnDrop<'_, '_, T, F, A>
        where
            F: FnMut(&mut T) -> bool,
        {
            fn drop(&mut self) {
                unsafe {
                    if self.drain.idx < self.drain.old_len && self.drain.del > 0 {
                        // This is a pretty messed up state, and there isn't really an
                        // obviously right thing to do. We don't want to keep trying
                        // to execute `pred`, so we just backshift all the unprocessed
                        // elements and tell the vec that they still exist. The backshift
                        // is required to prevent a double-drop of the last successfully
                        // drained item prior to a panic in the predicate.
                        let ptr = self.drain.vec.as_mut_ptr();
                        let src = ptr.add(self.drain.idx);
                        let dst = src.sub(self.drain.del);
                        let tail_len = self.drain.old_len - self.drain.idx;
                        src.copy_to(dst, tail_len);
                    }
                    self.drain.vec.set_len(self.drain.old_len - self.drain.del);
                }
            }
        }

        let backshift = BackshiftOnDrop { drain: self };

        // Attempt to consume any remaining elements if the filter predicate
        // has not yet panicked. We'll backshift any remaining elements
        // whether we've already panicked or if the consumption here panics.
        if !backshift.drain.panic_flag {
            backshift.drain.for_each(drop);
        }
    }
}

unsafe fn arith_offset<T>(p: *const T, offset: isize) -> *const T {
    p.offset(offset)
}

fn partition_dedup_by<T, F>(s: &mut [T], mut same_bucket: F) -> (&mut [T], &mut [T])
where
    F: FnMut(&mut T, &mut T) -> bool,
{
    // Although we have a mutable reference to `s`, we cannot make
    // *arbitrary* changes. The `same_bucket` calls could panic, so we
    // must ensure that the slice is in a valid state at all times.
    //
    // The way that we handle this is by using swaps; we iterate
    // over all the elements, swapping as we go so that at the end
    // the elements we wish to keep are in the front, and those we
    // wish to reject are at the back. We can then split the slice.
    // This operation is still O(n).
    //
    // Example: We start in this state, where `r` represents "next
    // read" and `w` represents "next_write`.
    //
    //           r
    //     +---+---+---+---+---+---+
    //     | 0 | 1 | 1 | 2 | 3 | 3 |
    //     +---+---+---+---+---+---+
    //           w
    //
    // Comparing s[r] against s[w-1], this is not a duplicate, so
    // we swap s[r] and s[w] (no effect as r==w) and then increment both
    // r and w, leaving us with:
    //
    //               r
    //     +---+---+---+---+---+---+
    //     | 0 | 1 | 1 | 2 | 3 | 3 |
    //     +---+---+---+---+---+---+
    //               w
    //
    // Comparing s[r] against s[w-1], this value is a duplicate,
    // so we increment `r` but leave everything else unchanged:
    //
    //                   r
    //     +---+---+---+---+---+---+
    //     | 0 | 1 | 1 | 2 | 3 | 3 |
    //     +---+---+---+---+---+---+
    //               w
    //
    // Comparing s[r] against s[w-1], this is not a duplicate,
    // so swap s[r] and s[w] and advance r and w:
    //
    //                       r
    //     +---+---+---+---+---+---+
    //     | 0 | 1 | 2 | 1 | 3 | 3 |
    //     +---+---+---+---+---+---+
    //                   w
    //
    // Not a duplicate, repeat:
    //
    //                           r
    //     +---+---+---+---+---+---+
    //     | 0 | 1 | 2 | 3 | 1 | 3 |
    //     +---+---+---+---+---+---+
    //                       w
    //
    // Duplicate, advance r. End of slice. Split at w.

    let len = s.len();
    if len <= 1 {
        return (s, &mut []);
    }

    let ptr = s.as_mut_ptr();
    let mut next_read: usize = 1;
    let mut next_write: usize = 1;

    unsafe {
        // Avoid bounds checks by using raw pointers.
        while next_read < len {
            let ptr_read = ptr.add(next_read);
            let prev_ptr_write = ptr.add(next_write - 1);
            if !same_bucket(&mut *ptr_read, &mut *prev_ptr_write) {
                if next_read != next_write {
                    let ptr_write = prev_ptr_write.offset(1);
                    mem::swap(&mut *ptr_read, &mut *ptr_write);
                }
                next_write += 1;
            }
            next_read += 1;
        }
    }

    s.split_at_mut(next_write)
}

#[allow(clippy::cast_possible_wrap)]
unsafe fn offset_from<T>(p: *const T, origin: *const T) -> isize
where
    T: Sized,
{
    let pointee_size = mem::size_of::<T>();
    assert!(0 < pointee_size && isize::try_from(pointee_size).is_ok());

    // This is the same sequence that Clang emits for pointer subtraction.
    // It can be neither `nsw` nor `nuw` because the input is treated as
    // unsigned but then the output is treated as signed, so neither works.
    let d = isize::wrapping_sub(p as _, origin as _);
    d / (pointee_size as isize)
}

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}
