use crate::alloc::{AllocRef, BuildAlloc, LayoutErr, NonZeroLayout};
use core::fmt;

/// Augments `AllocErr` with a `CapacityOverflow` variant.
pub enum CollectionAllocErr<B: BuildAlloc>
where
    B::Ref: AllocRef,
{
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,

    /// The memory allocator returned an error
    AllocError {
        /// The layout of allocation request that failed
        layout: NonZeroLayout,

        /// Error returned by the allocator
        inner: <B::Ref as AllocRef>::Error,
    },
}

impl<B: BuildAlloc> fmt::Debug for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
    <B::Ref as AllocRef>::Error: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityOverflow => fmt.write_str("CapacityOverflow"),
            Self::AllocError { layout, inner } => fmt
                .debug_struct("AllocError")
                .field("layout", &layout)
                .field("inner", &inner)
                .finish(),
        }
    }
}

impl<B: BuildAlloc> Clone for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
    <B::Ref as AllocRef>::Error: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::CapacityOverflow => Self::CapacityOverflow,
            Self::AllocError { layout, inner } => Self::AllocError {
                layout: *layout,
                inner: inner.clone(),
            },
        }
    }
}

impl<B: BuildAlloc> PartialEq for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
    <B::Ref as AllocRef>::Error: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::CapacityOverflow, Self::CapacityOverflow) => true,
            (
                Self::AllocError { layout, inner },
                Self::AllocError {
                    layout: other_layout,
                    inner: other_inner,
                },
            ) => layout == other_layout && inner == other_inner,
            _ => false,
        }
    }
}

impl<B: BuildAlloc> Eq for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
    <B::Ref as AllocRef>::Error: Eq,
{
}

impl<B: BuildAlloc> From<core::alloc::LayoutErr> for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
{
    #[inline]
    fn from(_: core::alloc::LayoutErr) -> Self {
        Self::CapacityOverflow
    }
}

impl<B: BuildAlloc> From<LayoutErr> for CollectionAllocErr<B>
where
    B::Ref: AllocRef,
{
    #[inline]
    fn from(_: LayoutErr) -> Self {
        Self::CapacityOverflow
    }
}
