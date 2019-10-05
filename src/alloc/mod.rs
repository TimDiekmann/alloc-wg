mod abort;
mod layout;

pub use self::{
    abort::AbortAlloc,
    layout::{LayoutErr, NonZeroLayout},
};
use core::{
    alloc::{AllocErr, Layout},
    ptr::{self, NonNull},
};
use liballoc::alloc::{Alloc, Global};
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

macro_rules! impl_alloc_zst {
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

        impl AllocRef for $ty {
            type BuildAlloc = Self;
            type Error = AllocErr;

            fn get_build_alloc(&mut self) -> Self::BuildAlloc {
                Self
            }

            fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
                unsafe { Alloc::alloc(self, layout.into()) }
            }

            fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
                unsafe { Alloc::alloc_zeroed(self, layout.into()) }
            }
        }

        impl DeallocRef for $ty {
            type BuildDealloc = Self;

            fn get_build_dealloc(&mut self) -> Self::BuildDealloc {
                Self
            }

            unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
                Alloc::dealloc(self, ptr, layout.into())
            }
        }

        impl ReallocRef for $ty {
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
                Alloc::realloc(self, ptr, layout.into(), new_size)
            }
        }
    };
}

impl_alloc_zst!(Global);
#[cfg(feature = "std")]
impl_alloc_zst!(System);
