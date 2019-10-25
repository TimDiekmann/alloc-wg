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

/// The `CannotReallocInPlace` error is used when [`grow_in_place`] or
/// [`shrink_in_place`] were unable to reuse the given memory block for
/// a requested layout.
///
/// [`grow_in_place`]: ./trait.Alloc.html#method.grow_in_place
/// [`shrink_in_place`]: ./trait.Alloc.html#method.shrink_in_place
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CannotReallocInPlace;

impl CannotReallocInPlace {
    pub fn description(&self) -> &str {
        "cannot reallocate allocator's memory in place"
    }
}

// (we need this for downstream impl of trait Error)
impl fmt::Display for CannotReallocInPlace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.description())
    }
}

/// The `CannotReallocInPlace` error is used when [`grow_in_place`] or
/// [`shrink_in_place`] were unable to reuse the given memory block for
/// a requested layout.
///
/// [`grow_in_place`]: ./trait.Alloc.html#method.grow_in_place
/// [`shrink_in_place`]: ./trait.Alloc.html#method.shrink_in_place
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CapacityOverflow;

impl From<core::alloc::LayoutErr> for CapacityOverflow {
    #[inline]
    fn from(_: core::alloc::LayoutErr) -> Self {
        Self
    }
}

impl From<LayoutErr> for CapacityOverflow {
    #[inline]
    fn from(_: LayoutErr) -> Self {
        Self
    }
}

pub trait BuildAllocRef: Sized {
    type Ref: DeallocRef<BuildAlloc = Self>;

    unsafe fn build_alloc_ref(
        &mut self,
        ptr: NonNull<u8>,
        layout: Option<NonZeroLayout>,
    ) -> Self::Ref;
}

pub trait DeallocRef: Sized {
    type BuildAlloc: BuildAllocRef<Ref = Self>;

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

    fn usable_size(&self, layout: NonZeroLayout) -> (usize, usize) {
        (layout.size(), layout.size())
    }

    unsafe fn grow_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> bool {
        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_size >= layout.size());
        let (_l, u) = self.usable_size(layout);
        // _l <= layout.size()                       [guaranteed by usable_size()]
        //       layout.size() <= new_layout.size()  [required by this method]
        new_size <= u
    }

    unsafe fn shrink_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: usize,
    ) -> bool {
        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_size <= layout.size());
        let (l, _u) = self.usable_size(layout);
        //                      layout.size() <= _u  [guaranteed by usable_size()]
        // new_layout.size() <= layout.size()        [required by this method]
        l <= new_size
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
        impl BuildAllocRef for $ty {
            type Ref = Self;

            unsafe fn build_alloc_ref(
                &mut self,
                _ptr: NonNull<u8>,
                _layout: Option<NonZeroLayout>,
            ) -> Self::Ref {
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
