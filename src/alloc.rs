//! Memory allocation APIs

pub use liballoc::alloc::*;

use core::ptr::NonNull;

pub trait BuildAllocRef {
    type AllocRef: AllocRef;

    unsafe fn build_alloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::AllocRef;
}

impl BuildAllocRef for Global {
    type AllocRef = Self;

    unsafe fn build_alloc_ref(&mut self, _ptr: NonNull<u8>, _layout: Layout) -> Self::AllocRef {
        Self
    }
}

#[cfg(feature = "std")]
impl BuildAllocRef for std::alloc::System {
    type AllocRef = Self;

    unsafe fn build_alloc_ref(&mut self, _ptr: NonNull<u8>, _layout: Layout) -> Self::AllocRef {
        Self
    }
}
