#![allow(clippy::use_self)]

use crate::alloc::{
    handle_alloc_error,
    AllocRef,
    BuildAllocRef,
    DeallocRef,
    NonZeroLayout,
    NonZeroUsize,
    ReallocRef,
};
use core::ptr::NonNull;

/// An allocator adapter that blows up by calling `handle_alloc_error` on OOM.
///
/// On one hand, concrete allocator implementations should always be written
/// without panicking on user error and OOM to give users maximum
/// flexibility. On the other hand, code that depends on allocation succeeding
/// should depend on `Alloc<Err=!>` to avoid repetitively handling errors from
/// which it cannot recover.
///
/// This adapter bridges the gap, effectively allowing `Alloc<Err=!>` to be
/// implemented by any allocator.
#[derive(Copy, Clone, Debug, Default)]
pub struct AbortAlloc<Alloc>(pub Alloc);

impl<A: BuildAllocRef> BuildAllocRef for AbortAlloc<A> {
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
    type Error = !;

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

    fn usable_size(&self, layout: NonZeroLayout) -> (usize, usize) {
        self.0.usable_size(layout)
    }

    unsafe fn grow_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: NonZeroUsize,
    ) -> bool {
        self.0.grow_in_place(ptr, layout, new_size)
    }

    unsafe fn shrink_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: NonZeroUsize,
    ) -> bool {
        self.0.shrink_in_place(ptr, layout, new_size)
    }
}

impl<A: ReallocRef> ReallocRef for AbortAlloc<A> {
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: NonZeroLayout,
        new_layout: NonZeroLayout,
    ) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .realloc(ptr, old_layout, new_layout)
            .map_err(|_| handle_alloc_error(new_layout.into()))
    }
}
