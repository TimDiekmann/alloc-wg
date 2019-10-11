#![allow(clippy::use_self)]

use crate::alloc::{AllocRef, BuildAlloc, DeallocRef, NonZeroLayout, ReallocRef};
use core::ptr::NonNull;
use liballoc::alloc::handle_alloc_error;

/// An allocator, which wraps another allocator and aborts on OOM.
#[derive(Default, Copy, Clone)]
pub struct AbortAlloc<A>(pub A);

impl<A: BuildAlloc> BuildAlloc for AbortAlloc<A> {
    type Ref = AbortAlloc<A::Ref>;

    unsafe fn build_alloc_ref(
        &mut self,
        ptr: NonNull<u8>,
        layout: Option<NonZeroLayout>,
    ) -> Self::Ref {
        Self(self.0.build_alloc_ref(ptr, layout))
    }
}

impl<A: DeallocRef> DeallocRef for AbortAlloc<A> {
    type BuildAlloc = AbortAlloc<A::BuildAlloc>;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        Self(self.0.get_build_alloc())
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        self.0.dealloc(ptr, layout)
    }
}

impl<A: AllocRef> AllocRef for AbortAlloc<A> {
    type Error = crate::Never;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .alloc(layout)
            .map_err(|_| handle_alloc_error(layout.into()))
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .alloc_zeroed(layout)
            .map_err(|_| handle_alloc_error(layout.into()))
    }
}

impl<A: ReallocRef> ReallocRef for AbortAlloc<A> {
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .realloc(ptr, layout, new_size)
            .map_err(|_| handle_alloc_error(layout.into()))
    }
}
