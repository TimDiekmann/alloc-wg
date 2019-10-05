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
#[allow(clippy::module_name_repetitions)]
pub mod alloc;

extern crate alloc as liballoc;

mod unchecked_unwrap;
pub use self::unchecked_unwrap::*;

pub type Never = core::convert::Infallible;
