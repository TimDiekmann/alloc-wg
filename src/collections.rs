use crate::alloc::{AllocRef, CapacityOverflow, LayoutErr, NonZeroLayout};

/// Augments `AllocErr` with a `CapacityOverflow` variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollectionAllocErr<A: AllocRef> {
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,

    /// The memory allocator returned an error
    AllocError {
        /// The layout of allocation request that failed
        layout: NonZeroLayout,

        /// Error returned by the allocator
        inner: A::Error,
    },
}

impl<A: AllocRef> From<CapacityOverflow> for CollectionAllocErr<A> {
    #[inline]
    #[must_use]
    fn from(_: CapacityOverflow) -> Self {
        Self::CapacityOverflow
    }
}

impl<A: AllocRef> From<LayoutErr> for CollectionAllocErr<A> {
    #[inline]
    #[must_use]
    fn from(_: LayoutErr) -> Self {
        Self::CapacityOverflow
    }
}
