//! Memory allocation APIs

pub use core::alloc::{AllocErr, GlobalAlloc, Layout, LayoutErr};
pub use liballoc::alloc::{alloc, alloc_zeroed, dealloc, handle_alloc_error, realloc, Global};
#[cfg(feature = "std")]
pub use std::alloc::System;

use crate::{capacity_overflow, collections::TryReserveError};
use core::{
    intrinsics,
    ptr::{self, NonNull},
};

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
#[derive(Debug, Copy, Clone)]
pub struct MemoryBlock {
    pub ptr: NonNull<u8>,
    pub size: usize,
}

impl MemoryBlock {
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
            offset <= self.size,
            "`offset` must be smaller than or equal to `size()`"
        );
        match init {
            AllocInit::Uninitialized => (),
            AllocInit::Zeroed => self
                .ptr
                .as_ptr()
                .add(offset)
                .write_bytes(0, self.size - offset),
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
/// ### Currently allocated memory
///
/// Some of the methods require that a memory block be *currently allocated* via an allocator. This
/// means that:
///
/// * the starting address for that memory block was previously returned by [`alloc`], [`grow`], or
///   [`shrink`], and
///
/// * the memory block has not been subsequently deallocated, where blocks are either deallocated
///   directly by being passed to [`dealloc`] or were changed by being passed to [`grow`] or
///   [`shrink`] that returns `Ok`. If `grow` or `shrink` have returned `Err`, the passed pointer
///   remains valid.
///
/// [`alloc`]: AllocRef::alloc
/// [`grow`]: AllocRef::grow
/// [`shrink`]: AllocRef::shrink
/// [`dealloc`]: AllocRef::dealloc
///
/// ### Memory fitting
///
/// Some of the methods require that a layout *fit* a memory block. What it means for a layout to
/// "fit" a memory block means (or equivalently, for a memory block to "fit" a layout) is that the
/// following conditions must hold:
///
/// * The block must be allocated with the same alignment as [`layout.align()`], and
///
/// * The provided [`layout.size()`] must fall in the range `min ..= max`, where:
///   - `min` is the size of the layout most recently used to allocate the block, and
///   - `max` is the latest actual size returned from [`alloc`], [`grow`], or [`shrink`].
///
/// [`layout.align()`]: Layout::align
/// [`layout.size()`]: Layout::size
///
/// # Safety
///
/// * Memory blocks returned from an allocator must point to valid memory and retain their validity
///   until the instance and all of its clones are dropped, and
///
/// * cloning or moving the allocator must not invalidate memory blocks returned from this
///   allocator. A cloned allocator must behave like the same allocator.
///
/// * any pointer to a memory block which is [*currently allocated*] may be passed to any other
///   method of the allocator.
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
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout);

    /// Attempts to extend the memory block.
    ///
    /// Returns a new memory block containing a pointer and the actual size of the allocated
    /// block. The pointer is suitable for holding data described by a new layout with `layout`’s
    /// alignment and a size given by `new_size`. To accomplish this, the allocator may extend the
    /// allocation referenced by `ptr` to fit the new layout. If the [`placement`] is
    /// [`InPlace`], the returned pointer is guaranteed to be the same as the passed `ptr`.
    ///
    /// If `ReallocPlacement::MayMove` is used then ownership of the memory block referenced by `ptr`
    /// is transferred to this allocator. The memory may or may not be freed, and should be
    /// considered unusable (unless of course it is transferred back to the caller again via the
    /// return value of this method).
    ///
    /// If this method returns `Err`, then ownership of the memory block has not been transferred to
    /// this allocator, and the contents of the memory block are unaltered.
    ///
    /// The memory block will contain the following contents after a successful call to `grow`:
    ///   * Bytes `0..layout.size()` are preserved from the original allocation.
    ///   * Bytes `layout.size()..old_size` will either be preserved or initialized according to
    ///     [`init`], depending on the allocator implementation. `old_size` refers to the size of
    ///     the `MemoryBlock` prior to the `grow` call, which may be larger than the size
    ///     that was originally requested when it was allocated.
    ///   * Bytes `old_size..new_size` are initialized according to [`init`]. `new_size` refers to
    ///     the size of the `MemoryBlock` returned by the `grow` call.
    ///
    /// [`InPlace`]: ReallocPlacement::InPlace
    /// [`placement`]: ReallocPlacement
    /// [`init`]: AllocInit
    ///
    /// # Safety
    ///
    /// * `ptr` must be [*currently allocated*] via this allocator,
    /// * `layout` must [*fit*] the `ptr`. (The `new_size` argument need not fit it.)
    // We can't require that `new_size` is strictly greater than `memory.size()` because of ZSTs.
    // An alternative would be
    // * `new_size must be strictly greater than `memory.size()` or both are zero
    /// * `new_size` must be greater than or equal to `layout.size()`
    /// * `new_size`, when rounded up to the nearest multiple of `layout.align()`, must not overflow
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
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<MemoryBlock, AllocErr> {
        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove => {
                let size = layout.size();
                debug_assert!(
                    new_size >= size,
                    "`new_size` must be greater than or equal to `layout.size()`"
                );

                if new_size == size {
                    return Ok(MemoryBlock { ptr, size });
                }

                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                let new_memory = self.alloc(new_layout, init)?;
                ptr::copy_nonoverlapping(ptr.as_ptr(), new_memory.ptr.as_ptr(), size);
                self.dealloc(ptr, layout);
                Ok(new_memory)
            }
        }
    }

    /// Attempts to shrink the memory block.
    ///
    /// Returns a new memory block containing a pointer and the actual size of the allocated
    /// block. The pointer is suitable for holding data described by a new layout with `layout`’s
    /// alignment and a size given by `new_size`. To accomplish this, the allocator may shrink the
    /// allocation referenced by `ptr` to fit the new layout. If the [`placement`] is
    /// [`InPlace`], the returned pointer is guaranteed to be the same as the passed `ptr`.
    ///
    /// If this returns `Ok`, then ownership of the memory block referenced by `ptr` has been
    /// transferred to this allocator. The memory may or may not have been freed, and should be
    /// considered unusable unless it was transferred back to the caller again via the
    /// return value of this method.
    ///
    /// If this method returns `Err`, then ownership of the memory block has not been transferred to
    /// this allocator, and the contents of the memory block are unaltered.
    ///
    /// The behavior of how the allocator tries to shrink the memory is specified by [`placement`].
    ///
    /// [`InPlace`]: ReallocPlacement::InPlace
    /// [`placement`]: ReallocPlacement
    ///
    /// # Safety
    ///
    /// * `ptr` must be [*currently allocated*] via this allocator,
    /// * `layout` must [*fit*] the `ptr`. (The `new_size` argument need not fit it.)
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
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<MemoryBlock, AllocErr> {
        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove => {
                let size = layout.size();
                debug_assert!(
                    new_size <= size,
                    "`new_size` must be smaller than or equal to `layout.size()`"
                );

                if new_size == size {
                    return Ok(MemoryBlock { ptr, size });
                }

                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                let new_memory = self.alloc(new_layout, AllocInit::Uninitialized)?;
                ptr::copy_nonoverlapping(ptr.as_ptr(), new_memory.ptr.as_ptr(), new_size);
                self.dealloc(ptr, layout);
                Ok(new_memory)
            }
        }
    }
}

unsafe impl AllocRef for Global {
    #[inline]
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        unsafe {
            let size = layout.size();
            if size == 0 {
                Ok(MemoryBlock {
                    ptr: layout.dangling(),
                    size: 0,
                })
            } else {
                let raw_ptr = match init {
                    AllocInit::Uninitialized => alloc(layout),
                    AllocInit::Zeroed => alloc_zeroed(layout),
                };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocErr)?;
                Ok(MemoryBlock { ptr, size })
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            dealloc(ptr.as_ptr(), layout)
        }
    }

    #[inline]
    unsafe fn grow(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size >= size,
            "`new_size` must be greater than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if layout.size() == 0 => {
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                self.alloc(new_layout, init)
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size > old_size` or something similar.
                intrinsics::assume(new_size > size);
                let ptr = realloc(ptr.as_ptr(), layout, new_size);
                let mut memory = MemoryBlock {
                    ptr: NonNull::new(ptr).ok_or(AllocErr)?,
                    size: new_size,
                };
                memory.init_offset(init, size);
                Ok(memory)
            }
        }
    }

    #[inline]
    unsafe fn shrink(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size <= size,
            "`new_size` must be smaller than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if new_size == 0 => {
                self.dealloc(ptr, layout);
                Ok(MemoryBlock {
                    ptr: layout.dangling(),
                    size: 0,
                })
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size < old_size` or something similar.
                intrinsics::assume(new_size < size);
                let ptr = realloc(ptr.as_ptr(), layout, new_size);
                Ok(MemoryBlock {
                    ptr: NonNull::new(ptr).ok_or(AllocErr)?,
                    size: new_size,
                })
            }
        }
    }
}

#[cfg(feature = "std")]
unsafe impl AllocRef for System {
    #[inline]
    fn alloc(&mut self, layout: Layout, init: AllocInit) -> Result<MemoryBlock, AllocErr> {
        unsafe {
            let size = layout.size();
            if size == 0 {
                Ok(MemoryBlock {
                    ptr: layout.dangling(),
                    size: 0,
                })
            } else {
                let raw_ptr = match init {
                    AllocInit::Uninitialized => GlobalAlloc::alloc(self, layout),
                    AllocInit::Zeroed => GlobalAlloc::alloc_zeroed(self, layout),
                };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocErr)?;
                Ok(MemoryBlock { ptr, size })
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            GlobalAlloc::dealloc(self, ptr.as_ptr(), layout)
        }
    }

    #[inline]
    unsafe fn grow(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
        init: AllocInit,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size >= size,
            "`new_size` must be greater than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if layout.size() == 0 => {
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                self.alloc(new_layout, init)
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size > old_size` or something similar.
                intrinsics::assume(new_size > size);
                let ptr = GlobalAlloc::realloc(self, ptr.as_ptr(), layout, new_size);
                let mut memory = MemoryBlock {
                    ptr: NonNull::new(ptr).ok_or(AllocErr)?,
                    size: new_size,
                };
                memory.init_offset(init, size);
                Ok(memory)
            }
        }
    }

    #[inline]
    unsafe fn shrink(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
        placement: ReallocPlacement,
    ) -> Result<MemoryBlock, AllocErr> {
        let size = layout.size();
        debug_assert!(
            new_size <= size,
            "`new_size` must be smaller than or equal to `memory.size()`"
        );

        if size == new_size {
            return Ok(MemoryBlock { ptr, size });
        }

        match placement {
            ReallocPlacement::InPlace => Err(AllocErr),
            ReallocPlacement::MayMove if new_size == 0 => {
                self.dealloc(ptr, layout);
                Ok(MemoryBlock {
                    ptr: layout.dangling(),
                    size: 0,
                })
            }
            ReallocPlacement::MayMove => {
                // `realloc` probably checks for `new_size < old_size` or something similar.
                intrinsics::assume(new_size < size);
                let ptr = GlobalAlloc::realloc(self, ptr.as_ptr(), layout, new_size);
                Ok(MemoryBlock {
                    ptr: NonNull::new(ptr).ok_or(AllocErr)?,
                    size: new_size,
                })
            }
        }
    }
}
