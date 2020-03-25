//! Memory allocation APIs

pub use core::alloc::{GlobalAlloc, Layout, LayoutErr};
pub use liballoc::alloc::{alloc, alloc_zeroed, dealloc, handle_alloc_error, realloc};
#[cfg(feature = "std")]
pub use std::alloc::System;

use crate::{capacity_overflow, collections::TryReserveError, ptr::Unique};
use core::{
    fmt,
    intrinsics,
    mem,
    ptr::{self, NonNull},
};

/// The `AllocErr` error indicates an allocation failure
/// that may be due to resource exhaustion or to
/// something wrong when combining the given input arguments with this
/// allocator.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AllocErr;

// (we need this for downstream impl of trait Error)
impl fmt::Display for AllocErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("memory allocation failed")
    }
}

/// A desired initial state for allocated memory.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AllocInit {
    /// The contents of the new memory are undefined.
    ///
    /// Reading uninitialized memory is Undefined Behavior; it must be initialized before use.
    Uninitialized,
    /// The new memory is guaranteed to be zeroed.
    Zeroed,
}

/// Represents a block of allocated memory returned by an allocator.
#[derive(Debug)]
#[must_use = "`MemoryBlock` should be passed to `AllocRef::dealloc`"]
pub struct MemoryBlock {
    ptr: Unique<u8>,
    layout: Layout,
}

impl MemoryBlock {
    /// Creates a new `MemoryBlock`.
    ///
    /// # Safety
    ///
    /// * The block must be allocated with the same alignment as [`layout.align()`], and
    /// * The provided [`layout.size()`] must fall in the range `min ..= max`, where:
    ///   - `min` is the size requested size when allocating the block, and
    ///   - `max` is the size of the memory block.
    #[inline]
    pub const unsafe fn new(ptr: NonNull<u8>, layout: Layout) -> Self {
        Self {
            ptr: Unique::new_unchecked(ptr.as_ptr()),
            layout,
        }
    }

    /// Acquires the underlying `NonNull<u8>` pointer.
    #[inline]
    pub const fn ptr(&self) -> NonNull<u8> {
        // SAFETY: Unique<T> is always non-null
        unsafe { NonNull::new_unchecked(self.ptr.as_ptr()) }
    }

    /// Returns the layout describing the memory block.
    #[inline]
    pub const fn layout(&self) -> Layout {
        self.layout
    }

    /// Returns the size of the memory block.
    #[inline]
    pub const fn size(&self) -> usize {
        self.layout().size()
    }

    /// Returns the minimum alignment of the memory block.
    #[inline]
    pub const fn align(&self) -> usize {
        self.layout().align()
    }

    /// Initialize the memory block like specified by `init`.
    ///
    /// This behaves like calling [`MemoryBlock::initialize_offset(ptr, layout, 0)`][off].
    ///
    /// [off]: MemoryBlock::init_offset
    ///
    /// [*fit*]: trait.AllocRef.html#memory-fitting
    #[inline]
    pub fn init(&mut self, init: AllocInit) {
        // SAFETY: 0 is always smaller or equal to the size
        unsafe { self.init_offset(init, 0) }
    }

    /// Initialize the memory block like specified by `init` at the specified `offset`.
    ///
    /// This is a no-op for [`AllocInit::Uninitialized`] and writes zeroes for [`AllocInit::Zeroed`]
    /// at `ptr + offset` until `ptr + layout.size()`.
    ///
    /// # Safety
    ///
    /// * `offset` must be smaller than or equal to `size()`
    ///
    /// [*fit*]: trait.AllocRef.html#memory-fitting
    #[inline]
    pub unsafe fn init_offset(&mut self, init: AllocInit, offset: usize) {
        debug_assert!(
            offset <= self.size(),
            "`offset` must be smaller than or equal to `size()`"
        );
        match init {
            AllocInit::Uninitialized => (),
            AllocInit::Zeroed => self
                .ptr()
                .as_ptr()
                .add(offset)
                .write_bytes(0, self.size() - offset),
        }
    }
}

/// A placement constraint when growing or shrinking an existing allocation.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ReallocPlacement {
    /// The allocator is allowed to move the allocation to a different memory address.
    // FIXME(wg-allocators#46): Add a section to the module documentation "What is a legal
    //                          allocator" and link it at "valid location".
    ///
    /// If the allocation _does_ move, it's the responsibility of the allocator
    /// to also move the data from the previous location to the new location.
    MayMove,
    /// The address of the new memory must not change.
    ///
    /// If the allocation would have to be moved to a new location to fit, the
    /// reallocation request will fail.
    InPlace,
}

/// An implementation of `AllocRef` can allocate, grow, shrink, and deallocate arbitrary blocks of
/// data described via [`Layout`][].
///
/// `AllocRef` is designed to be implemented on ZSTs, references, or smart pointers because having
/// an allocator like `MyAlloc([u8; N])` cannot be moved, without updating the pointers to the
/// allocated memory.
///
/// Unlike [`GlobalAlloc`][], zero-sized allocations are allowed in `AllocRef`. If an underlying
/// allocator does not support this (like jemalloc) or return a null pointer (such as
/// `libc::malloc`), this case must be caught.
///
/// # Safety
///
/// * Memory blocks returned from an allocator must point to valid memory and retain their validity
///   until the instance and all of its clones are dropped, and
///
/// * cloning or moving the allocator must not invalidate memory blocks returned from this
///   allocator. A cloned allocator must behave like the same allocator.
///
/// [*currently allocated*]: #currently-allocated-memory
pub unsafe trait AllocRef {
    /// On success, returns a memory block meeting the size and alignment guarantees of `layout`.
    ///
    /// The returned block may have a larger size than specified by `layout.size()` and is
    /// initialized as specified by [`init`], all the way up to the returned size of the block.
    ///
    /// [`init`]: AllocInit
    ///
    /// # Errors
    ///
    /// Returning `Err` indicates that either memory is exhausted or `layout` does not meet
    /// allocator's size or alignment constraints.
    ///
    /// Implementations are encouraged to return `Err` on memory exhaustion rather than panicking or
    /// aborting, but this is not a strict requirement. (Specifically: it is *legal* to implement
    /// this trait atop an underlying native allocation library that aborts on memory exhaustion.)
    ///
    /// Clients wishing to abort computation in response to an allocation error are encouraged to
    /// call the [`handle_alloc_error`] function, rather than directly invoking `panic!` or similar.
    ///
    /// [`handle_alloc_error`]: ../../alloc/alloc/fn.handle_alloc_error.html
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr>;

    /// Deallocates the memory denoted by `memory`.
    ///
    /// # Safety
    ///
    /// `memory` must be a memory block returned by this allocator.
    unsafe fn dealloc(&mut self, memory: MemoryBlock);

    /// Attempts to extend the memory block.
    ///
    /// The behavior of how the allocator tries to grow the memory is specified by [`placement`].
    /// The first `memory.size()` bytes are preserved or copied as appropriate from `ptr`, and the
    /// remaining bytes up to the new `memory.size()` are initialized according to [`init`].
    ///
    /// [`placement`]: ReallocPlacement
    /// [`init`]: AllocInit
    ///
    /// # Safety
    ///
    /// * `memory` must be a memory block returned by this allocator.
    // We can't require that `new_size` is strictly greater than `memory.size()` because of ZSTs.
    // An alternative would be
    // * `new_size must be strictly greater than `memory.size()` or both are zero
    /// * `new_size` must be greater than or equal to `memory.size()`
    /// * `new_size`, when rounded up to the nearest multiple of `memory.align()`, must not overflow
    ///   (i.e., the rounded value must be less than `usize::MAX`).
    ///
    /// [*currently allocated*]: #currently-allocated-memory
    /// [*fit*]: #memory-fitting
    ///
    /// # Errors
    ///
    /// Returns `Err` if the new layout does not meet the allocator's size and alignment
    /// constraints of the allocator, or if growing otherwise fails.
    ///
    /// Implementations are encouraged to return `Err` on memory exhaustion rather than panicking or
    /// aborting, but this is not a strict requirement. (Specifically: it is *legal* to implement
    /// this trait atop an underlying native allocation library that aborts on memory exhaustion.)
    ///
    /// Clients wishing to abort computation in response to an allocation error are encouraged to
    /// call the [`handle_alloc_error`] function, rather than directly invoking `panic!` or similar.
    ///
    /// [`handle_alloc_error`]: ../../alloc/alloc/fn.handle_alloc_error.html
    unsafe fn grow(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<(), AllocErr> {
        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove => {
                let old_size = memory.size();
                debug_assert!(
                    new_size > old_size,
                    "`new_size` must be greater than or equal to `memory.size()`"
                );

                if new_size == old_size {
                    return Ok(());
                }

                let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
                let new_memory = self.alloc(new_layout, init)?;
                ptr::copy_nonoverlapping(
                    memory.ptr().as_ptr(),
                    new_memory.ptr().as_ptr(),
                    old_size,
                );
                self.dealloc(mem::replace(memory, new_memory));
                Ok(())
            }
        }
    }

    /// Attempts to shrink the memory block.
    ///
    /// The behavior of how the allocator tries to shrink the memory is specified by [`placement`].
    ///
    /// [`placement`]: ReallocPlacement
    ///
    /// # Safety
    ///
    /// * `memory` must be a memory block returned by this allocator.
    // We can't require that `new_size` is strictly smaller than `memory.size()` because of ZSTs.
    // An alternative would be
    // * `new_size must be strictly smaller than `memory.size()` or both are zero
    /// * `new_size` must be smaller than or equal to `memory.size()`
    ///
    /// [*currently allocated*]: #currently-allocated-memory
    /// [*fit*]: #memory-fitting
    ///
    /// # Errors
    ///
    /// Returns `Err` if the new layout does not meet the allocator's size and alignment
    /// constraints of the allocator, or if growing otherwise fails.
    ///
    /// Implementations are encouraged to return `Err` on memory exhaustion rather than panicking or
    /// aborting, but this is not a strict requirement. (Specifically: it is *legal* to implement
    /// this trait atop an underlying native allocation library that aborts on memory exhaustion.)
    ///
    /// Clients wishing to abort computation in response to an allocation error are encouraged to
    /// call the [`handle_alloc_error`] function, rather than directly invoking `panic!` or similar.
    ///
    /// [`handle_alloc_error`]: ../../alloc/alloc/fn.handle_alloc_error.html
    unsafe fn shrink(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<(), AllocErr> {
        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove => {
                let old_size = memory.size();
                debug_assert!(
                    new_size <= old_size,
                    "`new_size` must be smaller than or equal to `layout.size()`"
                );

                if new_size == old_size {
                    return Ok(());
                }

                let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
                let new_memory = self.alloc(new_layout, AllocInit::Uninitialized)?;
                ptr::copy_nonoverlapping(
                    memory.ptr().as_ptr(),
                    new_memory.ptr().as_ptr(),
                    new_size,
                );
                self.dealloc(mem::replace(memory, new_memory));
                Ok(())
            }
        }
    }
}

/// The global memory allocator.
///
/// This type implements the [`AllocRef`][] trait by forwarding calls
/// to the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// Note: while this type is unstable, the functionality it provides can be
/// accessed through the [free functions in `alloc`](index.html#functions).
#[derive(Copy, Clone, Debug, Default)]
pub struct Global;

unsafe impl AllocRef for Global {
    #[inline]
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        unsafe {
            if layout.size() == 0 {
                Ok(MemoryBlock::new(layout.dangling(), layout))
            } else {
                let raw_ptr = match init {
                    AllocInit::Uninitialized => alloc(layout),
                    AllocInit::Zeroed => alloc_zeroed(layout),
                };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocErr)?;
                Ok(MemoryBlock::new(ptr, layout))
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&mut self, memory: MemoryBlock) {
        if memory.size() != 0 {
            dealloc(memory.ptr().as_ptr(), memory.layout())
        }
    }

    #[inline]
    unsafe fn grow(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<(), AllocErr> {
        let old_size = memory.size();
        debug_assert!(
            new_size >= old_size,
            "`new_size` must be greater than or equal to `memory.size()`"
        );

        if old_size == new_size {
            return Ok(());
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
        match placement {
            ReallocPlacement::InPlace => return Err(AllocErr),
            ReallocPlacement::MayMove if memory.size() == 0 => {
                *memory = self.alloc(new_layout, init)?
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size > old_size` or something similar.
                intrinsics::assume(new_size > old_size);
                let ptr = realloc(memory.ptr().as_ptr(), memory.layout(), new_size);
                *memory = MemoryBlock::new(NonNull::new(ptr).ok_or(AllocErr)?, new_layout);
                memory.init_offset(init, old_size);
            }
        }
        Ok(())
    }

    #[inline]
    unsafe fn shrink(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<(), AllocErr> {
        let old_size = memory.size();
        debug_assert!(
            new_size <= old_size,
            "`new_size` must be smaller than or equal to `memory.size()`"
        );

        if old_size == new_size {
            return Ok(());
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
        match placement {
            ReallocPlacement::InPlace => return Err(AllocErr),
            ReallocPlacement::MayMove if new_size == 0 => {
                let new_memory = MemoryBlock::new(new_layout.dangling(), new_layout);
                let old_memory = mem::replace(memory, new_memory);
                self.dealloc(old_memory)
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size < old_size` or something similar.
                intrinsics::assume(new_size < old_size);
                let ptr = realloc(memory.ptr().as_ptr(), memory.layout(), new_size);
                *memory = MemoryBlock::new(NonNull::new(ptr).ok_or(AllocErr)?, new_layout);
            }
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
unsafe impl AllocRef for System {
    #[inline]
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        unsafe {
            if layout.size() == 0 {
                Ok(MemoryBlock::new(layout.dangling(), layout))
            } else {
                let raw_ptr = match init {
                    AllocInit::Uninitialized => GlobalAlloc::alloc(self, layout),
                    AllocInit::Zeroed => GlobalAlloc::alloc_zeroed(self, layout),
                };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocErr)?;
                Ok(MemoryBlock::new(ptr, layout))
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&mut self, memory: MemoryBlock) {
        if memory.size() != 0 {
            GlobalAlloc::dealloc(self, memory.ptr().as_ptr(), memory.layout())
        }
    }

    #[inline]
    unsafe fn grow(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<(), AllocErr> {
        let old_size = memory.size();
        debug_assert!(
            new_size >= old_size,
            "`new_size` must be greater than or equal to `memory.size()`"
        );

        if old_size == new_size {
            return Ok(());
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
        match placement {
            ReallocPlacement::InPlace => return Err(AllocErr),
            ReallocPlacement::MayMove if memory.size() == 0 => {
                *memory = self.alloc(new_layout, init)?
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size > old_size` or something similar.
                intrinsics::assume(new_size > old_size);
                let ptr =
                    GlobalAlloc::realloc(self, memory.ptr().as_ptr(), memory.layout(), new_size);
                *memory = MemoryBlock::new(NonNull::new(ptr).ok_or(AllocErr)?, new_layout);
                memory.init_offset(init, old_size);
            }
        }
        Ok(())
    }

    #[inline]
    unsafe fn shrink(
        &mut self,
        memory: &mut MemoryBlock,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<(), AllocErr> {
        let old_size = memory.size();
        debug_assert!(
            new_size >= old_size,
            "`new_size` must be smaller than or equal to `memory.size()`"
        );

        if old_size == new_size {
            return Ok(());
        }

        let new_layout = Layout::from_size_align_unchecked(new_size, memory.align());
        match placement {
            ReallocPlacement::InPlace => return Err(AllocErr),
            ReallocPlacement::MayMove if new_size == 0 => {
                let new_memory = MemoryBlock::new(new_layout.dangling(), new_layout);
                let old_memory = mem::replace(memory, new_memory);
                self.dealloc(old_memory)
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size < old_size` or something similar.
                intrinsics::assume(new_size < old_size);
                let ptr =
                    GlobalAlloc::realloc(self, memory.ptr().as_ptr(), memory.layout(), new_size);
                *memory = MemoryBlock::new(NonNull::new(ptr).ok_or(AllocErr)?, new_layout);
            }
        }
        Ok(())
    }
}

pub(crate) fn handle_reserve_error<T>(result: Result<T, TryReserveError>) -> T {
    match result {
        Ok(t) => t,
        Err(TryReserveError::AllocError { layout }) => handle_alloc_error(layout),
        Err(TryReserveError::CapacityOverflow) => capacity_overflow(),
    }
}
