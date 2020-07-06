//! Collection types.

use crate::alloc::{Layout, LayoutErr};
use core::fmt::Display;
pub use liballoc::collections::{binary_heap, btree_set, linked_list, vec_deque};

pub mod btree_map {
    pub use super::super::btree::map::*;
}

#[doc(no_inline)]
pub use self::{
    binary_heap::BinaryHeap,
    btree_map::BTreeMap,
    btree_set::BTreeSet,
    linked_list::LinkedList,
    vec_deque::VecDeque,
};

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
