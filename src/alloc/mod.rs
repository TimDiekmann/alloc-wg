mod abort;
mod layout;

pub use self::{
    abort::AbortAlloc,
    layout::{LayoutErr, NonZeroLayout},
};
pub use core::alloc::{GlobalAlloc, Layout};
use core::{
    fmt,
    ptr::{self, NonNull},
};
pub use liballoc::alloc::{alloc, alloc_zeroed, dealloc, realloc};
#[cfg(feature = "std")]
use std::alloc::System;

pub trait BuildAlloc: Sized {
    type AllocRef: AllocRef<BuildAlloc = Self>;

    unsafe fn build_alloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::AllocRef;
}

pub trait BuildDealloc: Sized {
    type DeallocRef: DeallocRef<BuildDealloc = Self>;

    unsafe fn build_dealloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::DeallocRef;
}

pub trait BuildRealloc: Sized {
    type ReallocRef: ReallocRef<BuildRealloc = Self>;

    unsafe fn build_realloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::ReallocRef;
}

pub trait AllocRef: Sized {
    type BuildAlloc: BuildAlloc<AllocRef = Self>;
    type Error;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error>;

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        let size = layout.size();
        let p = self.alloc(layout)?;
        unsafe {
            ptr::write_bytes(p.as_ptr(), 0, size);
        }
        Ok(p)
    }
}

pub trait DeallocRef: Sized {
    type BuildDealloc: BuildDealloc<DeallocRef = Self>;

    fn get_build_dealloc(&mut self) -> Self::BuildDealloc;

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout);
}

pub trait ReallocRef: Sized {
    type BuildRealloc: BuildRealloc<ReallocRef = Self>;
    type Error;

    fn get_build_realloc(&mut self) -> Self::BuildRealloc;

    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> Result<NonNull<u8>, Self::Error>;
}

/// The `AllocErr` error indicates an allocation failure
/// that may be due to resource exhaustion or to
/// something wrong when combining the given input arguments with this
/// allocator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AllocErr;

impl fmt::Display for AllocErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

/// The global memory allocator.
///
/// This type implements the allocation traits by forwarding calls
/// to the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
#[derive(Copy, Clone, Default, Debug)]
pub struct Global;

macro_rules! impl_common_alloc_zst {
    ($ty:tt) => {
        impl BuildAlloc for $ty {
            type AllocRef = Self;

            unsafe fn build_alloc_ref(
                &mut self,
                _ptr: NonNull<u8>,
                _layout: Layout,
            ) -> Self::AllocRef {
                Self
            }
        }

        impl BuildDealloc for $ty {
            type DeallocRef = Self;

            unsafe fn build_dealloc_ref(
                &mut self,
                _ptr: NonNull<u8>,
                _layout: Layout,
            ) -> Self::DeallocRef {
                Self
            }
        }

        impl BuildRealloc for $ty {
            type ReallocRef = Self;

            unsafe fn build_realloc_ref(
                &mut self,
                _ptr: NonNull<u8>,
                _layout: Layout,
            ) -> Self::ReallocRef {
                Self
            }
        }
    };
}

impl_common_alloc_zst!(Global);
#[cfg(feature = "std")]
impl_common_alloc_zst!(System);

impl AllocRef for Global {
    type BuildAlloc = Self;
    type Error = AllocErr;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        Self
    }

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(alloc(layout.into())).ok_or(AllocErr) }
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(alloc_zeroed(layout.into())).ok_or(AllocErr) }
    }
}

impl DeallocRef for Global {
    type BuildDealloc = Self;

    fn get_build_dealloc(&mut self) -> Self::BuildDealloc {
        Self
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        dealloc(ptr.as_ptr(), layout.into())
    }
}

impl ReallocRef for Global {
    type BuildRealloc = Self;
    type Error = AllocErr;

    fn get_build_realloc(&mut self) -> Self::BuildRealloc {
        Self
    }

    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> Result<NonNull<u8>, Self::Error> {
        NonNull::new(realloc(ptr.as_ptr(), layout.into(), new_size)).ok_or(AllocErr)
    }
}

#[cfg(feature = "std")]
impl AllocRef for System {
    type BuildAlloc = Self;
    type Error = AllocErr;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        Self
    }

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(GlobalAlloc::alloc(self, layout.into())).ok_or(AllocErr) }
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(GlobalAlloc::alloc_zeroed(self, layout.into())).ok_or(AllocErr) }
    }
}

#[cfg(feature = "std")]
impl DeallocRef for System {
    type BuildDealloc = Self;

    fn get_build_dealloc(&mut self) -> Self::BuildDealloc {
        Self
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.into())
    }
}

#[cfg(feature = "std")]
impl ReallocRef for System {
    type BuildRealloc = Self;
    type Error = AllocErr;

    fn get_build_realloc(&mut self) -> Self::BuildRealloc {
        Self
    }

    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> Result<NonNull<u8>, Self::Error> {
        NonNull::new(GlobalAlloc::realloc(
            self,
            ptr.as_ptr(),
            layout.into(),
            new_size,
        ))
        .ok_or(AllocErr)
    }
}
