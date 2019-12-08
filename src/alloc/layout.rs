pub use core::alloc::Layout;
use core::{
    convert::{TryFrom, TryInto},
    fmt,
    mem,
    num::NonZeroUsize,
};

/// The parameters given to `Layout::from_size_align` or some other `Layout` constructor do not
/// satisfy its documented constraints.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutErr {
    private: (),
}

impl From<core::alloc::LayoutErr> for LayoutErr {
    #[must_use]
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
pub struct NonZeroLayout {
    // size of the requested block of memory, measured in bytes.
    size: NonZeroUsize,

    // alignment of the requested block of memory, measured in bytes.
    // we ensure that this is always a power-of-two, because API's
    // like `posix_memalign` require it and it is a reasonable
    // constraint to impose on Layout constructors.
    //
    // (However, we do not analogously require `align >= sizeof(void*)`,
    //  even though that is *also* a requirement of `posix_memalign`.)
    align: NonZeroUsize,
}

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
    #[must_use]
    pub const unsafe fn from_size_align_unchecked(size: NonZeroUsize, align: NonZeroUsize) -> Self {
        Self { size, align }
    }

    /// The minimum size in bytes for a memory block of this layout.
    #[inline]
    #[must_use]
    pub const fn size(&self) -> NonZeroUsize {
        self.size
    }

    /// The minimum byte alignment for a memory block of this layout.
    #[inline]
    #[must_use]
    pub const fn align(&self) -> NonZeroUsize {
        self.align
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
    #[must_use]
    pub const unsafe fn new_unchecked<T>() -> Self {
        Self::from_size_align_unchecked(
            NonZeroUsize::new_unchecked(mem::size_of::<T>()),
            NonZeroUsize::new_unchecked(mem::align_of::<T>()),
        )
    }

    /// Produces layout describing a record that could be used to allocate backing structure
    /// for `T` (which could be a trait or other unsized type like a slice).
    ///
    /// Returns `None` if `T` is a ZST.
    #[inline]
    pub fn for_value<T: ?Sized>(t: &T) -> Option<Self> {
        Layout::for_value(t).try_into().ok()
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
    #[must_use]
    pub const fn padding_needed_for(&self, align: NonZeroUsize) -> usize {
        // Rounded up value is:
        //   len_rounded_up = (len + align - 1) & !(align - 1);
        // and then we return the padding difference: `len_rounded_up - len`.
        //
        // We use modular arithmetic throughout:
        //
        // 1. align is guaranteed to be > 0, so align - 1 is always valid.
        //
        // 2. `len + align - 1` can overflow by at most `align - 1`, so the &-mask wth
        //    `!(align - 1)` will ensure that in the    case of overflow, `len_rounded_up` will
        // itself be 0.    Thus the returned padding, when added to `len`, yields 0, which
        // trivially satisfies    the alignment `align`.
        //
        // (Of course, attempts to allocate blocks of memory whose size and padding overflow in the
        // above manner should cause the allocator to yield an error anyway.)

        let len = self.size().get();
        let align = align.get();
        let len_rounded_up = len.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1);
        len_rounded_up.wrapping_sub(len)
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
        debug_assert_ne!(mem::size_of_val(t), 0);
        debug_assert_ne!(mem::align_of_val(t), 0);
        Self::from_size_align_unchecked(
            NonZeroUsize::new_unchecked(mem::size_of_val(t)),
            NonZeroUsize::new_unchecked(mem::align_of_val(t)),
        )
    }

    /// Creates a layout describing the record for `n` instances of `self`, with a suitable amount
    /// of padding between each to ensure that each instance is given its requested size and
    /// alignment. On success, returns `(k, offs)` where `k` is the layout of the array and
    /// `offs` is the distance between the start of each element in the array.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn repeat(&self, n: NonZeroUsize) -> Result<(Self, NonZeroUsize), LayoutErr> {
        let padded_size = self
            .size()
            .get()
            .checked_add(self.padding_needed_for(self.align()))
            .ok_or(LayoutErr { private: () })?;
        let alloc_size = padded_size
            .checked_mul(n.get())
            .ok_or(LayoutErr { private: () })?;

        unsafe {
            // self.align is already known to be valid and alloc_size has been
            // padded already.
            debug_assert_ne!(alloc_size, 0);
            debug_assert_ne!(padded_size, 0);
            Ok((
                Self::from_size_align_unchecked(
                    NonZeroUsize::new_unchecked(alloc_size),
                    self.align(),
                ),
                NonZeroUsize::new_unchecked(padded_size),
            ))
        }
    }

    /// Creates a layout describing the record for a `[T; n]`.
    ///
    /// On arithmetic overflow, returns `LayoutErr`.
    #[inline]
    pub fn array<T>(n: NonZeroUsize) -> Result<Self, LayoutErr> {
        Self::new::<T>()?.repeat(n).map(|(k, offs)| {
            debug_assert_eq!(offs.get(), mem::size_of::<T>());
            k
        })
    }
}

impl From<NonZeroLayout> for Layout {
    #[must_use]
    fn from(layout: NonZeroLayout) -> Self {
        unsafe { Self::from_size_align_unchecked(layout.size().get(), layout.align().get()) }
    }
}

impl TryFrom<Layout> for NonZeroLayout {
    type Error = LayoutErr;

    fn try_from(layout: Layout) -> Result<Self, Self::Error> {
        unsafe {
            debug_assert_ne!(layout.align(), 0);
            Ok(Self::from_size_align_unchecked(
                NonZeroUsize::new(layout.size()).ok_or(LayoutErr { private: {} })?,
                NonZeroUsize::new_unchecked(layout.align()),
            ))
        }
    }
}
