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
    type Ref: DeallocRef<BuildAlloc = Self>;

    unsafe fn build_alloc_ref(&mut self, ptr: NonNull<u8>, layout: Layout) -> Self::Ref;
}

pub trait DeallocRef: Sized {
    type BuildAlloc: BuildAlloc<Ref = Self>;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc;

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout);
}

pub trait AllocRef: DeallocRef {
    type Error;

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

pub trait ReallocRef: AllocRef {
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

macro_rules! impl_buildalloc_alloc_zst {
    ($ty:tt) => {
        impl BuildAlloc for $ty {
            type Ref = Self;

            unsafe fn build_alloc_ref(&mut self, _ptr: NonNull<u8>, _layout: Layout) -> Self::Ref {
                Self
            }
        }
    };
}

impl_buildalloc_alloc_zst!(Global);
#[cfg(feature = "std")]
impl_buildalloc_alloc_zst!(System);

impl DeallocRef for Global {
    type BuildAlloc = Self;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        Self
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        dealloc(ptr.as_ptr(), layout.into())
    }
}

impl AllocRef for Global {
    type Error = AllocErr;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(alloc(layout.into())).ok_or(AllocErr) }
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(alloc_zeroed(layout.into())).ok_or(AllocErr) }
    }
}

impl ReallocRef for Global {
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
impl DeallocRef for System {
    type BuildAlloc = Self;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc {
        Self
    }

    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout) {
        GlobalAlloc::dealloc(self, ptr.as_ptr(), layout.into())
    }
}

#[cfg(feature = "std")]
impl AllocRef for System {
    type Error = AllocErr;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(GlobalAlloc::alloc(self, layout.into())).ok_or(AllocErr) }
    }

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        unsafe { NonNull::new(GlobalAlloc::alloc_zeroed(self, layout.into())).ok_or(AllocErr) }
    }
}

#[cfg(feature = "std")]
impl ReallocRef for System {
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
