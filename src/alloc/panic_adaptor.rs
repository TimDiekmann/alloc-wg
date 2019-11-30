//! An allocator adapter that blows up by calling `handle_alloc_error` on all errors.
//!
//! On one hand, concrete allocator implementations should always be written
//! without panicking on user error and OOM to give users maximum
//! flexibility. On the other hand, code that depends on allocation succeeding
//! should depend on `Alloc<Err=!>` to avoid repetitively handling errors from
//! which it cannot recover.
//!
//! This adapter bridges the gap, effectively allowing `Alloc<Err=!>` to be
//! implemented by any allocator.

use core::{ptr::NonNull, usize};

use crate::alloc::*;

/// An allocator adapter that blows up by calling `handle_alloc_error` on all errors.
///
/// See the [module-level documentation](../../std/abort_adapter/index.html) for more.
#[derive(Copy, Clone, Debug, Default)]
pub struct PanicAdapter<Alloc>(pub Alloc);

impl<B: BuildAllocRef> BuildAllocRef for PanicAdapter<B> {
    type Ref = PanicAdapter<B::Ref>;

    unsafe fn build_alloc_ref(
        &mut self,
        ptr: NonNull<u8>,
        layout: Option<NonZeroLayout>,
    ) -> Self::Ref {
        PanicAdapter(self.0.build_alloc_ref(ptr, layout))
    }
}

impl<A: DeallocRef> DeallocRef for PanicAdapter<A> {
    type BuildAlloc = PanicAdapter<A::BuildAlloc>;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        PanicAdapter(self.0.get_build_alloc())
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        self.0.dealloc(ptr, layout)
    }
}

impl<A: AllocRef> AllocRef for PanicAdapter<A> {
    type Error = !;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .alloc(layout)
            .or_else(|_| handle_alloc_error(layout.into()))
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .alloc_zeroed(layout)
            .or_else(|_| handle_alloc_error(layout.into()))
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

impl<A: ReallocRef> ReallocRef for PanicAdapter<A> {
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: NonZeroLayout,
        new_layout: NonZeroLayout,
    ) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .realloc(ptr, old_layout, new_layout)
            .or_else(|_| handle_alloc_error(new_layout.into()))
    }
}
