mod abort;
mod layout;

pub use self::{
    abort::AbortAlloc,
    layout::{LayoutErr, NonZeroLayout},
};
pub use core::alloc::GlobalAlloc;
use core::{
    cmp,
    fmt,
    num::NonZeroUsize,
    ptr::{self, NonNull},
};
pub use liballoc::alloc::{alloc, alloc_zeroed, dealloc, realloc};
#[cfg(feature = "std")]
use std::alloc::System;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CapacityOverflow;

impl From<core::alloc::LayoutErr> for CapacityOverflow {
    #[inline]
    #[must_use]
    fn from(_: core::alloc::LayoutErr) -> Self {
        Self
    }
}

impl From<LayoutErr> for CapacityOverflow {
    #[inline]
    #[must_use]
    fn from(_: LayoutErr) -> Self {
        Self
    }
}

pub trait BuildAllocRef: Sized {
    type Ref: DeallocRef<BuildAlloc = Self>;

    #[must_use]
    /// # Safety
    ///
    /// * `ptr` must denote a block of memory currently allocated via this allocator
    /// * `layout` must *fit* that block of memory
    /// * the alignment of the `layout` must match the alignment used to allocate that block of
    ///   memory
    unsafe fn build_alloc_ref(
        &mut self,
        ptr: NonNull<u8>,
        layout: Option<NonZeroLayout>,
    ) -> Self::Ref;
}

pub trait DeallocRef: Sized {
    type BuildAlloc: BuildAllocRef<Ref = Self>;

    fn get_build_alloc(&mut self) -> Self::BuildAlloc;

    /// # Safety
    ///
    /// * `ptr` must denote a block of memory currently allocated via this allocator
    /// * `layout` must *fit* that block of memory
    /// * the alignment of the `layout` must match the alignment used to allocate that block of
    ///   memory
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: NonZeroLayout);
}

pub trait AllocRef: DeallocRef {
    type Error;

    fn alloc(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error>;

    fn alloc_zeroed(&mut self, layout: NonZeroLayout) -> Result<NonNull<u8>, Self::Error> {
        let size = layout.size();
        let p = self.alloc(layout)?;
        unsafe {
            ptr::write_bytes(p.as_ptr(), 0, size.get());
        }
        Ok(p)
    }

    fn usable_size(&self, layout: NonZeroLayout) -> (usize, usize) {
        (layout.size().get(), layout.size().get())
    }

    /// # Safety
    ///
    /// * `ptr` must be currently allocated via this allocator
    /// * `layout` must *fit* the `ptr` (see above); note the `new_size` argument need not fit it
    /// * `new_size` must not be less than `layout.size()`
    unsafe fn grow_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: NonZeroUsize,
    ) -> bool {
        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_size.get() >= layout.size().get());
        let (_l, u) = self.usable_size(layout);
        // _l <= layout.size()                       [guaranteed by usable_size()]
        //       layout.size() <= new_layout.size()  [required by this method]
        new_size.get() <= u
    }

    /// # Safety
    ///
    /// * `ptr` must be currently allocated via this allocator
    /// * `layout` must *fit* the `ptr` (see above); note the `new_size` argument need not fit it
    /// * `new_size` must not be greater than `layout.size()` (and must be greater than zero)
    unsafe fn shrink_in_place(
        &mut self,
        ptr: NonNull<u8>,
        layout: NonZeroLayout,
        new_size: NonZeroUsize,
    ) -> bool {
        let _ = ptr; // this default implementation doesn't care about the actual address.
        debug_assert!(new_size.get() <= layout.size().get());
        let (l, _u) = self.usable_size(layout);
        //                      layout.size() <= _u  [guaranteed by usable_size()]
        // new_layout.size() <= layout.size()        [required by this method]
        l <= new_size.get()
    }
}

pub trait ReallocRef: AllocRef {
    /// # Safety
    ///
    /// * `ptr` must be currently allocated via this allocator,
    /// * `layout` must *fit* the `ptr` (see above). (The `new_size` argument need not fit it.)
    /// * `new_size`, when rounded up to the nearest multiple of `layout.align()`,
    ///   must not overflow (i.e., the rounded value must be less than `usize::MAX`).
    ///
    /// (Extension subtraits might provide more specific bounds on
    /// behavior, e.g., guarantee a sentinel address or a null pointer
    /// in response to a zero-size allocation request.)
    ///
    /// # Errors
    ///
    /// Returns `Err` only if the new layout
    /// does not meet the allocator's size
    /// and alignment constraints of the allocator, or if reallocation
    /// otherwise fails.
    ///
    /// Implementations are encouraged to return `Err` on memory
    /// exhaustion rather than panicking or aborting, but this is not
    /// a strict requirement. (Specifically: it is *legal* to
    /// implement this trait atop an underlying native allocation
    /// library that aborts on memory exhaustion.)
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: NonZeroLayout,
        new_layout: NonZeroLayout,
    ) -> Result<NonNull<u8>, Self::Error> {
        let old_size = old_layout.size();
        let new_size = new_layout.size();

        if old_layout.align() == new_layout.align()
            && ((new_size > old_size && self.grow_in_place(ptr, old_layout, new_size))
                || (new_size < old_size && self.shrink_in_place(ptr, old_layout, new_size)))
        {
            return Ok(ptr);
        }

        alloc_copy_dealloc(self, ptr, old_layout, new_layout)
    }
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
        old_layout: NonZeroLayout,
        new_layout: NonZeroLayout,
    ) -> Result<NonNull<u8>, Self::Error> {
        // FIXME: Remove `else` branch. This is needed, as std provides old method.
        if old_layout.align() == new_layout.align() {
            NonNull::new(realloc(
                ptr.as_ptr(),
                old_layout.into(),
                new_layout.size().get(),
            ))
            .ok_or(AllocErr)
        } else {
            alloc_copy_dealloc(self, ptr, old_layout, new_layout)
        }
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
    // FIXME: Remove `else` branch. This is needed, as std provides old method.
    unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        old_layout: NonZeroLayout,
        new_layout: NonZeroLayout,
    ) -> Result<NonNull<u8>, Self::Error> {
        if old_layout.align() == new_layout.align() {
            NonNull::new(GlobalAlloc::realloc(
                self,
                ptr.as_ptr(),
                old_layout.into(),
                new_layout.size().get(),
            ))
            .ok_or(AllocErr)
        } else {
            alloc_copy_dealloc(self, ptr, old_layout, new_layout)
        }
    }
}

#[inline]
unsafe fn alloc_copy_dealloc<A: ReallocRef>(
    alloc: &mut A,
    ptr: NonNull<u8>,
    old_layout: NonZeroLayout,
    new_layout: NonZeroLayout,
) -> Result<NonNull<u8>, A::Error> {
    let result = alloc.alloc(new_layout);

    if let Ok(new_ptr) = result {
        ptr::copy_nonoverlapping(
            ptr.as_ptr(),
            new_ptr.as_ptr(),
            cmp::min(old_layout.size().get(), new_layout.size().get()),
        );
        alloc.dealloc(ptr, old_layout);
    }
    result
}
