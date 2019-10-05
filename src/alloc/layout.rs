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
