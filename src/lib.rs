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
//! - The allocators has to be associated with [`BuildAllocRef`]. It is related to the allocator traits similar how
//!   [`BuildHasher`] is related to [`Hasher`]. Although the signatures are different, it makes an even more flexible
//!   allocator design possible.
//!
//!   Issue: [rust-lang/wg-allocators#12](https://github.com/rust-lang/wg-allocators/issues/12)
//!
//! - Added an associative error type to [`AllocRef`]. Besides adding the possibility of returning additional information on
//!   allocation failure, it's also possible to split the usage of the [`AllocRef`] into a fallible and an infallible case.
//!   Personally I think this is a pretty big deal, as kernel programmer can rely on allocation, which will never fail.
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
//! - Support reallocating to a different alignment.
//!
//!   Issue: [rust-lang/wg-allocators#5](https://github.com/rust-lang/wg-allocators/issues/5)
//!
//!
//! [`Alloc`]: https://doc.rust-lang.org/1.38.0/alloc/alloc/trait.Alloc.html
//! [`AllocRef`]: crate::alloc::AllocRef
//! [`AllocRef::alloc`]: crate::alloc::AllocRef::alloc
//! [`AllocRef::alloc_zeroed`]: crate::alloc::AllocRef::alloc_zeroed
//! [`Box`]: crate::boxed::Box
//! [`DeallocRef`]: crate::alloc::DeallocRef
//! [`ReallocRef`]: crate::alloc::ReallocRef
//! [`BuildAllocRef`]: crate::alloc::BuildAllocRef
//! [`BuildHasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.BuildHasher.html
//! [`Hasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.Hasher.html
//! [`NonZeroLayout`]: crate::alloc::NonZeroLayout

#![feature(
    dropck_eyepatch,
    coerce_unsized,
    const_if_match,
    core_intrinsics,
    ptr_internals,
    str_internals,
    dispatch_from_dyn,
    unsize,
    exact_size_is_empty,
    receiver_trait,
    const_generics,
    const_generic_impls_guard,
    unboxed_closures,
    specialization,
    trusted_len,
    unsized_locals,
    fn_traits,
    exhaustive_patterns
)]
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
#![allow(clippy::module_name_repetitions, incomplete_features)]

pub mod alloc;
pub mod boxed;
pub mod clone;
pub mod collections;
pub mod iter;
pub mod raw_vec;
pub mod str;
pub mod string;
pub mod vec;

extern crate alloc as liballoc;

pub use liballoc::{borrow, fmt, rc, slice, sync};

#[macro_export]
macro_rules! vec {
    ($($x:expr),*) => ({
        let mut v = $crate::vec::Vec::new();
        $( v.push($x); )*
        v
    });
    ($($x:expr,)*) => ($crate::vec![$($x),*]);
    ($elem:expr; $n:expr) => (
        $crate::vec::from_elem($elem, $n)
    );
    (in $alloc:expr) => {
        $crate::vec::Vec::new_in($alloc)
    };
    (in $alloc:expr; $($x:expr),*) => {{
        let mut v = $crate::vec::Vec::new_in($alloc);
        $( v.push($x); )*
        v
    }};
    (in $alloc:expr; $($x:expr,)*) => ($crate::vec![in $alloc; $($x),*]);
    (in $alloc:expr; $elem:expr; $n:expr) => {{
        $crate::vec::from_elem_in($elem, $n, $alloc)
    }};
    (try $($x:expr),*) => {{
        (|| -> Result<$crate::vec::Vec<_,_>, $crate::collections::CollectionAllocErr<_>> {
            let mut v = $crate::vec::Vec::new();
            $( v.try_push($x)?; )*
            Ok(v)
        })()
    }};
    (try $($x:expr,)*) => ($crate::vec![try $($x),*]);
    (try $elem:expr; $n:expr) => {{
        $crate::vec::try_from_elem_in($elem, $n, $crate::alloc::AbortAlloc<$crate::alloc::Global>)
    }};
    (try in $alloc:expr; $($x:expr),*) => {{
        (|| -> Result<$crate::vec::Vec<_,_>, $crate::collections::CollectionAllocErr<_>> {
            let mut v = $crate::vec::Vec::new_in($alloc);
            $( v.try_push($x)?; )*
            Ok(v)
        })()
    }};
    (try in $alloc:expr; $($x:expr,)*) => ($crate::vec![try in $alloc; $($x),*]);
    (try in $alloc:expr; $elem:expr; $n:expr) => {{
        $crate::vec::try_from_elem_in($elem, $n, $alloc)
    }};
}

#[macro_export]
macro_rules! format {
    ( in $alloc:expr, $fmt:expr, $($args:expr),* ) => {{
        use std::fmt::Write;
        let mut s = $crate::string::String::new_in($alloc);
        let _ = write!(&mut s, $fmt, $($args),*);
        s
    }};
    ( $fmt:expr, $($args:expr),* ) => {{
        use std::fmt::Write;
        let mut s = $crate::string::String::new();
        let _ = write!(&mut s, $fmt, $($args),*);
        s
    }}
}
