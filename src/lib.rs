//! An attempt to collect several proposals of [rust-lang/wg-allocators](https://github.com/rust-lang/wg-allocators) into a
//! MVP.
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
    alloc_layout_extra,
    alloc_error_hook,
    dropck_eyepatch,
    coerce_unsized,
    const_fn,
    const_if_match,
    const_panic,
    const_nonzero_int_methods,
    const_saturating_int_methods,
    const_alloc_layout,
    const_raw_ptr_to_usize_cast,
    core_intrinsics,
    str_internals,
    dispatch_from_dyn,
    unsize,
    exact_size_is_empty,
    receiver_trait,
    maybe_uninit_extra,
    ptr_internals,
    const_generics,
    const_generic_impls_guard,
    unboxed_closures,
    specialization,
    trusted_len,
    unsized_locals,
    fn_traits,
    exhaustive_patterns,
    never_type,
    structural_match
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
#![allow(
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    incomplete_features
)]

pub mod alloc;
pub mod boxed;
pub mod clone;
pub mod collections;
pub mod iter;
mod ptr;
pub mod raw_vec;
pub mod str;
pub mod string;
pub mod vec;

extern crate alloc as liballoc;

pub use liballoc::{borrow, fmt, rc, slice, sync};

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
pub(in crate) fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

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
