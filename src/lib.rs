//! An attempt to collect several proposals of [rust-lang/wg-allocators](https://github.com/rust-lang/wg-allocators) into a
//! MVP.
//!
//! Changes regarding the current `Alloc` trait
//! -------------------------------------------
//!
//! - The first thing to notice is, that [`Alloc`] was renamed to [`AllocRef`] in order to show that they are typically
//!   implemented for a reference or smart pointer or ZST, not directly for the type that actually holds the allocator’s
//!   state.
//!
//!   Issue on WG repository: [rust-lang/wg-allocators#8](https://github.com/rust-lang/wg-allocators/issues/8)
//!
//! - [`AllocRef`] was split up into [`AllocRef`], [`DeallocRef`], and [`ReallocRef`] to make more flexible allocators
//!   possible.
//!
//!   Issue: [rust-lang/wg-allocators#9](https://github.com/rust-lang/wg-allocators/issues/9)
//!
//! - The allocators has to be associated with [`BuildAlloc`]. It is related to the allocator traits similar how
//!   [`BuildHasher`] is related to [`Hasher`]. Although the signatures are different, it makes an even more flexible
//!   allocator design possible.
//!
//!   Issue: [rust-lang/wg-allocators#12](https://github.com/rust-lang/wg-allocators/issues/12)
//!
//! - Added an associative error type to [`AllocRef`]. Besides adding the possibility of returning additional information on
//!   allocation failure, it's also possible to split the usage of the [`AllocRef`] into a fallible and an infallible case.
//!   Personally I think this is a pretty big deal, as kernel programmer can rely on allocation, which will never fail. If
//!   an allocation can fail, only a `try_*_in` method may be available. To maintain backwards compatibility, [`AbortAlloc`]
//!   was introduced. [`AbortAlloc`] wraps another allocator, but aborts on OOM thus `AbortAlloc<Global>` may be used as
//!   default allocator for [`Box`] or `Vec`. To realize this, [`AbortAlloc`] implements `AllocRef<Error=!>`.
//!
//!   Issue: [rust-lang/wg-allocators#23](https://github.com/rust-lang/wg-allocators/issues/23)
//!
//! - The new layout type [`NonZeroLayout`] was introduced. Currently, implementors of [`Alloc`] can chose to allow
//!   zero-sized allocation so in a generic context it's impossible to rely on this, so banning zero-sized allocation is a
//!   possible step to prevent this. This also removes `unsafe` from [`AllocRef::alloc`] and [`AllocRef::alloc_zeroed`], and
//!   unlocks the possibility to move the extension API like `alloc_array` into a separate trait.
//!
//!   Issue: [rust-lang/wg-allocators#16](https://github.com/rust-lang/wg-allocators/issues/16)
//!
//!
//! [`Alloc`]: https://doc.rust-lang.org/1.38.0/alloc/alloc/trait.Alloc.html
//! [`AllocRef`]: crate::alloc::AllocRef
//! [`AllocRef::alloc`]: crate::alloc::AllocRef::alloc
//! [`AllocRef::alloc_zeroed`]: crate::alloc::AllocRef::alloc_zeroed
//! [`Box`]: crate::boxed::Box
//! [`DeallocRef`]: crate::alloc::DeallocRef
//! [`ReallocRef`]: crate::alloc::ReallocRef
//! [`BuildAlloc`]: crate::alloc::BuildAlloc
//! [`BuildHasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.BuildHasher.html
//! [`Hasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.Hasher.html
//! [`NonZeroLayout`]: crate::alloc::NonZeroLayout
//! [`AbortAlloc`]: crate::alloc::AbortAlloc

#![cfg_attr(feature = "dropck_eyepatch", feature(dropck_eyepatch))]
#![cfg_attr(feature = "ptr_internals", feature(ptr_internals))]
#![cfg_attr(not(feature = "std"), no_std)]
#![doc(test(attr(
    deny(
        future_incompatible,
        nonstandard_style,
        rust_2018_compatibility,
        rust_2018_idioms,
        unused,
        macro_use_extern_crate,
        trivial_casts,
        trivial_numeric_casts,
        unused_import_braces,
        unused_lifetimes,
        unused_qualifications,
        variant_size_differences,
    ),
    allow(unused_extern_crates)
)))]
#![warn(
    future_incompatible,
    nonstandard_style,
    rust_2018_compatibility,
    rust_2018_idioms,
    unused,
    macro_use_extern_crate,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications
)]
#![allow(clippy::module_name_repetitions)]

pub mod alloc;
pub mod boxed;
pub mod collections;
pub mod raw_vec;

extern crate alloc as liballoc;

mod unchecked_unwrap;
pub use self::unchecked_unwrap::*;

pub type Never = core::convert::Infallible;
