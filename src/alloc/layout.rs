pub use core::alloc::Layout;
use core::{
    convert::{TryFrom, TryInto},
    fmt,
    mem,
};

/// The parameters given to `Layout::from_size_align` or some other `Layout` constructor do not
/// satisfy its documented constraints.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutErr {
    private: (),
}

impl From<core::alloc::LayoutErr> for LayoutErr {
    fn from(_: core::alloc::LayoutErr) -> Self {
        Self { private: () }
    }
}

impl fmt::Display for LayoutErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid parameters to Layout::from_size_align")
    }
}

/// Non-zero Layout of a block of memory.
///
/// An instance of `NonZeroLayout` describes a particular layout of memory. You build a
/// `NonZeroLayout` up as an input to give to an allocator.
///
/// All layouts have an associated non-negative size and a power-of-two alignment.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NonZeroLayout(Layout);

impl NonZeroLayout {
    /// Constructs a `Layout` from a given `size` and `align`,
    /// or returns `LayoutErr` if either of the following conditions
    /// are not met:
    ///
    /// * `align` must not be zero,
    /// * `align` must be a power of two,
    /// * `size` must not be zero,
    /// * `size`, when rounded up to the nearest multiple of `align`, must not overflow (i.e., the
    ///   rounded value must be less than `usize::MAX`).
    #[inline]
    pub fn from_size_align(size: usize, align: usize) -> Result<Self, LayoutErr> {
        Layout::from_size_align(size, align)?.try_into()
    }

    /// Creates a layout, bypassing all checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe as it does not verify the preconditions from
    /// [`NonZeroLayout::from_size_align`][].
    #[inline]
    pub const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self {
        Self(Layout::from_size_align_unchecked(size, align))
    }

    /// The minimum size in bytes for a memory block of this layout.
    #[inline]
    pub fn size(&self) -> usize {
        self.0.size()
    }

    /// The minimum byte alignment for a memory block of this layout.
    #[inline]
    pub fn align(&self) -> usize {
        self.0.align()
    }

    /// Constructs a `NonZeroLayout` suitable for holding a value of type `T`.
    ///
    /// Returns `Err` if `T` is a ZST.
    #[inline]
    pub fn new<T>() -> Result<Self, LayoutErr> {
        Layout::new::<T>().try_into()
    }

    /// Constructs a `NonZeroLayout` suitable for holding a value of type `T`.
    ///
    /// # Safety
    ///
    /// This function is unsafe as it does not verify the preconditions from
    /// [`NonZeroLayout::new`][].
    #[inline]
    pub const unsafe fn new_unchecked<T>() -> Self {
        Self::from_size_align_unchecked(mem::size_of::<T>(), mem::align_of::<T>())
    }

    /// Produces layout describing a record that could be used to allocate backing structure
    /// for `T` (which could be a trait or other unsized type like a slice).
    ///
    /// Returns `Err` if `T` is a ZST.
    #[inline]
    pub fn for_value<T: ?Sized>(t: &T) -> Result<Self, LayoutErr> {
        Layout::for_value(t).try_into()
    }

    /// Produces layout describing a record that could be used to allocate backing structure
    /// for `T` (which could be a trait or other unsized type like a slice).
    ///
    /// # Safety
    ///
    /// This function is unsafe as it does not verify the preconditions from
    /// [`NonZeroLayout::for_value`][].
    #[inline]
    pub unsafe fn for_value_unchecked<T: ?Sized>(t: &T) -> Self {
        Self::from_size_align_unchecked(mem::size_of_val(t), mem::align_of_val(t))
    }

    /// Creates a layout describing the record that can hold a value of the same layout as `self`,
    /// but that also is aligned to alignment `align` (measured in bytes).
    ///
    /// If `self` already meets the prescribed alignment, then returns `self`.
    ///
    /// Note that this method does not add any padding to the overall size, regardless of whether
    /// the returned layout has a different alignment. In other words, if `K` has size 16,
    /// `K.align_to(32)` will *still* have size 16.
    ///
    /// Returns an error if the combination of `self.size()` and the given `align` violates the
    /// conditions listed in [`Layout::from_size_align`](#method.from_size_align).
    #[inline]
    pub fn align_to(&self, align: usize) -> Result<Self, LayoutErr> {
        self.0.align_to(align)?.try_into()
    }

    /// Returns the amount of padding we must insert after `self` to ensure that the following
    /// address will satisfy `align` (measured in bytes).
    ///
    /// e.g., if `self.size()` is 9, then `self.padding_needed_for(4)` returns 3, because that is
    /// the minimum number of bytes of padding required to get a 4-aligned address (assuming
    /// that the corresponding memory block starts at a 4-aligned address).
    ///
    /// The return value of this function has no meaning if `align` is not a power-of-two.
    ///
    /// Note that the utility of the returned value requires `align` to be less than or equal to the
    /// alignment of the starting address for the whole allocated block of memory. One way to
    /// satisfy this constraint is to ensure `align <= self.align()`.
    #[inline]
    pub fn padding_needed_for(&self, align: usize) -> usize {
        self.0.padding_needed_for(align)
    }

    /// Creates a layout by rounding the size of this layout up to a multiple of the layout's
    /// alignment.
    ///
    /// Returns `Err` if the padded size would overflow.
    ///
    /// This is equivalent to adding the result of `padding_needed_for` to the layout's current
    /// size.
    #[inline]
    pub fn pad_to_align(&self) -> Result<Self, LayoutErr> {
        self.0.pad_to_align()?.try_into()
    }

    /// Creates a layout describing the record for `n` instances of `self`, with a suitable amount
    /// of padding between each to ensure that each instance is given its requested size and
    /// alignment. On success, returns `(k, offs)` where `k` is the layout of the array and
    /// `offs` is the distance between the start of each element in the array.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn repeat(&self, n: usize) -> Result<(Self, usize), LayoutErr> {
        let (layout, size) = self.0.repeat(n)?;
        Ok((layout.try_into()?, size))
    }

    /// Creates a layout describing the record for `self` followed by `next`, including any
    /// necessary padding to ensure that `next` will be properly aligned. Note that the
    /// result layout will satisfy the alignment properties of both `self` and `next`.
    ///
    /// The resulting layout will be the same as that of a C struct containing two fields with the
    /// layouts of `self` and `next`, in that order.
    ///
    /// Returns `Some((k, offset))`, where `k` is layout of the concatenated record and `offset` is
    /// the relative location, in bytes, of the start of the `next` embedded within the
    /// concatenated record (assuming that the record itself starts at offset 0).
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn extend(&self, next: Self) -> Result<(Self, usize), LayoutErr> {
        let (layout, size) = self.0.extend(next.into())?;
        Ok((layout.try_into()?, size))
    }

    /// Creates a layout describing the record for `n` instances of `self`, with no padding between
    /// each instance.
    ///
    /// Note that, unlike `repeat`, `repeat_packed` does not guarantee that the repeated instances
    /// of `self` will be properly aligned, even if a given instance of `self` is properly
    /// aligned. In other words, if the layout returned by `repeat_packed` is used to allocate
    /// an array, it is not guaranteed that all elements in the array will be properly
    /// aligned.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn repeat_packed(&self, n: usize) -> Result<Self, LayoutErr> {
        self.0.repeat_packed(n)?.try_into()
    }

    /// Creates a layout describing the record for `self` followed by `next` with no additional
    /// padding between the two. Since no padding is inserted, the alignment of `next` is
    /// irrelevant, and is not incorporated *at all* into the resulting layout.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn extend_packed(&self, next: Self) -> Result<Self, LayoutErr> {
        self.0.extend_packed(next.into())?.try_into()
    }

    /// Creates a layout describing the record for a `[T; n]`.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn array<T>(n: usize) -> Result<Self, LayoutErr> {
        Layout::array::<T>(n)?.try_into()
    }
}

impl Into<Layout> for NonZeroLayout {
    fn into(self) -> Layout {
        unsafe { Layout::from_size_align_unchecked(self.size(), self.align()) }
    }
}

impl TryFrom<Layout> for NonZeroLayout {
    type Error = LayoutErr;

    fn try_from(layout: Layout) -> Result<Self, Self::Error> {
        let size = layout.size();
        if size == 0 {
            Err(LayoutErr { private: () })
        } else {
            unsafe { Ok(Self::from_size_align_unchecked(size, layout.align())) }
        }
    }
}
