//! Collection types.

use crate::alloc::{Layout, LayoutErr};
use core::fmt::Display;

/// The error type for `try_reserve` methods.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TryReserveError {
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,

    /// The memory allocator returned an error
    #[non_exhaustive]
    AllocError {
        /// The layout of allocation request that failed
        layout: Layout,
    },
}

impl From<LayoutErr> for TryReserveError {
    #[inline]
    fn from(_: LayoutErr) -> Self {
        Self::CapacityOverflow
    }
}

impl Display for TryReserveError {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        fmt.write_str("memory allocation failed")?;
        let reason = match &self {
            Self::CapacityOverflow => {
                " because the computed capacity exceeded the collection's maximum"
            }
            Self::AllocError { .. } => " because the memory allocator returned a error",
        };
        fmt.write_str(reason)
    }
}
