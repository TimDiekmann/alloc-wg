use crate::alloc::{
    AllocRef,
    BuildAlloc,
    BuildDealloc,
    BuildRealloc,
    DeallocRef,
    Layout,
    NonZeroLayout,
    ReallocRef,
};
use core::ptr::NonNull;

#[derive(Default, Copy, Clone)]
pub struct AbortAlloc<A>(pub A);

impl<A: BuildAlloc> BuildAlloc for AbortAlloc<A> {
    type AllocRef = AbortAlloc<A::AllocRef>;

    unsafe fn build_alloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::AllocRef {
        AbortAlloc(self.0.build_alloc_ref(ptr, layout))
    }
}

impl<A: BuildDealloc> BuildDealloc for AbortAlloc<A> {
    type DeallocRef = AbortAlloc<A::DeallocRef>;

    unsafe fn build_dealloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::DeallocRef {
        AbortAlloc(self.0.build_dealloc_ref(ptr, layout))
    }
}

impl<A: BuildRealloc> BuildRealloc for AbortAlloc<A> {
    type ReallocRef = AbortAlloc<A::ReallocRef>;

    unsafe fn build_realloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::ReallocRef {
        AbortAlloc(self.0.build_realloc_ref(ptr, layout))
    }
}

#[cold]
#[cfg(feature = "std")]
fn alloc_abort(layout: NonZeroLayout) -> ! {
    eprintln!("Allocator error with layout: {:?}", layout);
    std::process::abort()
}

#[cold]
#[cfg(not(feature = "std"))]
fn alloc_abort(_layout: NonZeroLayout) -> ! {
    unsafe { core::intrinsics::abort() }
}

impl<A: AllocRef> AllocRef for AbortAlloc<A> {
    type BuildAlloc = AbortAlloc<A::BuildAlloc>;
    type Error = !;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        AbortAlloc(self.0.get_build_alloc())
    }

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0.alloc(layout).map_err(|_| alloc_abort(layout))
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        self.0.alloc_zeroed(layout).map_err(|_| alloc_abort(layout))
    }
}

impl<A: DeallocRef> DeallocRef for AbortAlloc<A> {
    type BuildDealloc = AbortAlloc<A::BuildDealloc>;

    fn get_build_dealloc(&mut self) -> Self::BuildDealloc {
        AbortAlloc(self.0.get_build_dealloc())
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        self.0.dealloc(ptr, layout)
    }
}

impl<A: ReallocRef> ReallocRef for AbortAlloc<A> {
    type BuildRealloc = AbortAlloc<A::BuildRealloc>;
    type Error = !;

    fn get_build_realloc(&mut self) -> Self::BuildRealloc {
        AbortAlloc(self.0.get_build_realloc())
    }

    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> Result<NonNull<u8>, Self::Error> {
        self.0
            .realloc(ptr, layout, new_size)
            .map_err(|_| alloc_abort(layout))
    }
}
