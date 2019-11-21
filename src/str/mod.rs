//! Unicode string slices.
//!
//! *[See also the `str` primitive type][str].*
//!
//! The `&str` type is one of the two main string types, the other being `String`.
//! Unlike its `String` counterpart, its contents are borrowed.
//!
//! # Basic Usage
//!
//! A basic string declaration of `&str` type:
//!
//! ```
//! # #![allow(unused_variables)]
//! let hello_world = "Hello, World!";
//! ```
//!
//! Here we have declared a string literal, also known as a string slice.
//! String literals have a static lifetime, which means the string `hello_world`
//! is guaranteed to be valid for the duration of the entire program.
//! We can explicitly specify `hello_world`'s lifetime as well:
//!
//! ```
//! # #![allow(unused_variables)]
//! let hello_world: &'static str = "Hello, world!";
//! ```
//!
//! [str]: https://doc.rust-lang.org/nightly/std/primitive.str.html

// pub use core::str::pattern;
use crate::{
    alloc::DeallocRef,
    borrow::{Borrow, BorrowMut},
    boxed::Box,
    string::String,
};
#[allow(deprecated)]
pub use liballoc::str::LinesAny;
pub use liballoc::str::{
    from_utf8,
    from_utf8_mut,
    from_utf8_unchecked,
    from_utf8_unchecked_mut,
    Bytes,
    CharIndices,
    Chars,
    EncodeUtf16,
    EscapeDebug,
    EscapeDefault,
    EscapeUnicode,
    FromStr,
    Lines,
    MatchIndices,
    Matches,
    ParseBoolError,
    RMatchIndices,
    RMatches,
    RSplit,
    RSplitN,
    RSplitTerminator,
    Split,
    SplitAsciiWhitespace,
    SplitN,
    SplitTerminator,
    SplitWhitespace,
    Utf8Error,
};

impl<D: DeallocRef> Borrow<str> for String<D> {
    #[inline]
    fn borrow(&self) -> &str {
        &self[..]
    }
}

impl<D: DeallocRef> BorrowMut<str> for String<D> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        &mut self[..]
    }
}

/// Converts a boxed slice of bytes to a boxed string slice without checking
/// that the string contains valid UTF-8.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use alloc_wg::boxed::Box;
///
/// let smile_utf8 = Box::new([226, 152, 186]);
/// let smile = unsafe { alloc_wg::str::from_boxed_utf8_unchecked(smile_utf8) };
///
/// assert_eq!("☺", &*smile);
/// ```
#[allow(clippy::missing_safety_doc)]
#[inline]
pub unsafe fn from_boxed_utf8_unchecked<A: DeallocRef>(v: Box<[u8], A>) -> Box<str, A> {
    let a = core::ptr::read(v.build_alloc());
    Box::from_raw_in(Box::into_raw(v) as *mut str, a)
}
