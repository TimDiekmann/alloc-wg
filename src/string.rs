//! A UTF-8 encoded, growable string.
//!
//! This module contains the [`String`] type, a trait for converting
//! [`ToString`]s, and several error types that may result from working with
//! [`String`]s.
//!
//! [`ToString`]: trait.ToString.html
//!
//! # Examples
//!
//! There are multiple ways to create a new [`String`] from a string literal:
//!
//! ```unused_variables
//! # use alloc_wg::string::String;
//! let s = String::from("Hello");
//! let s = String::from("world");
//! let s: String = "also this".into();
//! ```
//!
//! You can create a new [`String`] from an existing one by concatenating with
//! `+`:
//!
//! [`String`]: struct.String.html
//!
//! ```unused_variables
//! # use alloc_wg::string::String;
//! let s = String::from("Hello");
//!
//! let message = s + " world!";
//! ```
//!
//! If you have a vector of valid UTF-8 bytes, you can make a [`String`] out of
//! it. You can do the reverse too.
//!
//! ```
//! # use alloc_wg::string::String;
//! # use alloc_wg::vec;
//! let sparkle_heart = vec![240, 159, 146, 150];
//!
//! // We know these bytes are valid, so we'll use `unwrap()`.
//! let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
//!
//! assert_eq!("💖", sparkle_heart);
//!
//! let bytes = sparkle_heart.into_bytes();
//!
//! assert_eq!(bytes, [240, 159, 146, 150]);
//! ```

use core::{
    char::{decode_utf16, REPLACEMENT_CHARACTER},
    fmt,
    hash,
    iter::{FromIterator, FusedIterator},
    ops::{
        self,
        Add,
        AddAssign,
        Bound::{Excluded, Included, Unbounded},
        Index,
        IndexMut,
        RangeBounds,
    },
    ptr,
    str::{self, Chars, FromStr, Utf8Error},
};

use crate::{
    alloc::{AbortAlloc, AllocRef, DeallocRef, Global, ReallocRef},
    boxed::Box,
    collect::TryExtend,
    collections::CollectionAllocErr,
    str::{from_boxed_utf8_unchecked, lossy},
    vec::Vec,
};

#[cfg(feature = "std")]
use std::borrow::Cow;

/// A UTF-8 encoded, growable string.
///
/// The `String` type is the most common string type that has ownership over the
/// contents of the string. It has a close relationship with its borrowed
/// counterpart, the primitive [`str`].
///
/// [`str`]: ../../std/primitive.str.html
///
/// # Examples
///
/// You can create a `String` from a literal string with [`String::from`]:
///
/// ```unused_variables
/// # use alloc_wg::string::String;
/// let hello = String::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a `String` with the [`push`] method, and
/// append a [`&str`] with the [`push_str`] method:
///
/// ```
/// # use alloc_wg::string::String;
/// let mut hello = String::from("Hello, ");
///
/// hello.push('w');
/// hello.push_str("orld!");
/// ```
///
/// [`String::from`]: #method.from
/// [`char`]: ../../std/primitive.char.html
/// [`push`]: #method.push
/// [`push_str`]: #method.push_str
///
/// If you have a vector of UTF-8 bytes, you can create a `String` from it with
/// the [`from_utf8`] method:
///
/// ```
/// # use alloc_wg::string::String;
/// # use alloc_wg::vec;
/// // some bytes, in a vector
/// let sparkle_heart = vec![240, 159, 146, 150];
///
/// // We know these bytes are valid, so we'll use `unwrap()`.
/// let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
///
/// assert_eq!("💖", sparkle_heart);
/// ```
///
/// [`from_utf8`]: #method.from_utf8
///
/// # UTF-8
///
/// `String`s are always valid UTF-8. This has a few implications, the first of
/// which is that if you need a non-UTF-8 string, consider [`OsString`]. It is
/// similar, but without the UTF-8 constraint. The second implication is that
/// you cannot index into a `String`:
///
/// ```compile_fail,E0277
/// let s = "hello";
///
/// println!("The first letter of s is {}", s[0]); // ERROR!!!
/// ```
///
/// [`OsString`]: ../../std/ffi/struct.OsString.html
///
/// Indexing is intended to be a constant-time operation, but UTF-8 encoding
/// does not allow us to do this. Furthermore, it's not clear what sort of
/// thing the index should return: a byte, a codepoint, or a grapheme cluster.
/// The [`bytes`] and [`chars`] methods return iterators over the first
/// two, respectively.
///
/// [`bytes`]: #method.bytes
/// [`chars`]: #method.chars
///
/// # Deref
///
/// `String`s implement [`Deref`]`<Target=str>`, and so inherit all of [`str`]'s
/// methods. In addition, this means that you can pass a `String` to a
/// function which takes a [`&str`] by using an ampersand (`&`):
///
/// ```unused_variables
/// # use alloc_wg::string::String;
///
/// fn takes_str(s: &str) {}
///
/// let s = String::from("Hello");
///
/// takes_str(&s);
/// ```
///
/// This will create a [`&str`] from the `String` and pass it in. This
/// conversion is very inexpensive, and so generally, functions will accept
/// [`&str`]s as arguments unless they need a `String` for some specific
/// reason.
///
/// In certain cases Rust doesn't have enough information to make this
/// conversion, known as [`Deref`] coercion. In the following example a string
/// slice [`&'a str`][`&str`] implements the trait `TraitExample`, and the function
/// `example_func` takes anything that implements the trait. In this case Rust
/// would need to make two implicit conversions, which Rust doesn't have the
/// means to do. For that reason, the following example will not compile.
///
/// ```compile_fail,E0277
/// # use alloc_wg::string::String;
///
/// trait TraitExample {}
///
/// impl<'a> TraitExample for &'a str {}
///
/// fn example_func<A: TraitExample>(example_arg: A) {}
///
/// let example_string = String::from("example_string");
/// example_func(&example_string);
/// ```
///
/// There are two options that would work instead. The first would be to
/// change the line `example_func(&example_string);` to
/// `example_func(example_string.as_str());`, using the method [`as_str()`]
/// to explicitly extract the string slice containing the string. The second
/// way changes `example_func(&example_string);` to
/// `example_func(&*example_string);`. In this case we are dereferencing a
/// `String` to a [`str`][`&str`], then referencing the [`str`][`&str`] back to
/// [`&str`]. The second way is more idiomatic, however both work to do the
/// conversion explicitly rather than relying on the implicit conversion.
///
/// # Representation
///
/// A `String` is made up of three components: a pointer to some bytes, a
/// length, and a capacity. The pointer points to an internal buffer `String`
/// uses to store its data. The length is the number of bytes currently stored
/// in the buffer, and the capacity is the size of the buffer in bytes. As such,
/// the length will always be less than or equal to the capacity.
///
/// This buffer is always stored on the heap.
///
/// You can look at these with the [`as_ptr`], [`len`], and [`capacity`]
/// methods:
///
/// ```
/// # use alloc_wg::string::String;
/// use std::mem;
///
/// let story = String::from("Once upon a time...");
// FIXME Update this when vec_into_raw_parts is stabilized
/// // Prevent automatically dropping the String's data
/// let mut story = mem::ManuallyDrop::new(story);
///
/// let ptr = story.as_mut_ptr();
/// let len = story.len();
/// let capacity = story.capacity();
///
/// // story has nineteen bytes
/// assert_eq!(19, len);
///
/// // We can re-build a String out of ptr, len, and capacity. This is all
/// // unsafe because we are responsible for making sure the components are
/// // valid:
/// let s = unsafe { String::from_raw_parts(ptr, len, capacity) } ;
///
/// assert_eq!(String::from("Once upon a time..."), s);
/// ```
/// 
/// [`as_ptr`]: #method.as_ptr
/// [`len`]: #method.len
/// [`capacity`]: #method.capacity
///
/// If a `String` has enough capacity, adding elements to it will not
/// re-allocate. For example, consider this program:
/// ```
/// # use alloc_wg::string::String;
/// let mut s = String::new();
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
/// 
/// This will output the following:
/// ```text
/// 0
/// 5
/// 10
/// 20
/// 20
/// 40
/// ```
/// 
/// At first, we have no memory allocated at all, but as we append to the
/// string, it increases its capacity appropriately. If we instead use the
/// [`with_capacity`] method to allocate the correct capacity initially:
/// ```
/// # use alloc_wg::string::String;
/// let mut s = String::with_capacity(25);
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
/// 
/// [`with_capacity`]: #method.with_capacity
///
/// We end up with a different output:
/// ```text
/// 25
/// 25
/// 25
/// 25
/// 25
/// 25
/// ```
/// 
/// Here, there's no need to allocate more memory inside the loop.
///
/// [`&str`]: ../../std/primitive.str.html
/// [`Deref`]: ../../std/ops/trait.Deref.html
/// [`as_str()`]: struct.String.html#method.as_str
#[derive(PartialOrd, Eq, Ord)]
pub struct String<A: DeallocRef = AbortAlloc<Global>> {
    vec: Vec<u8, A>,
}

/// A possible error value when converting a `String` from a UTF-8 byte vector.
///
/// This type is the error type for the [`from_utf8`] method on [`String`]. It
/// is designed in such a way to carefully avoid reallocations: the
/// [`into_bytes`] method will give back the byte vector that was used in the
/// conversion attempt.
///
/// [`from_utf8`]: struct.String.html#method.from_utf8
/// [`String`]: struct.String.html
/// [`into_bytes`]: struct.FromUtf8Error.html#method.into_bytes
///
/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
/// an analogue to `FromUtf8Error`, and you can get one from a `FromUtf8Error`
/// through the [`utf8_error`] method.
///
/// [`Utf8Error`]: ../../std/str/struct.Utf8Error.html
/// [`std::str`]: ../../std/str/index.html
/// [`u8`]: ../../std/primitive.u8.html
/// [`&str`]: ../../std/primitive.str.html
/// [`utf8_error`]: #method.utf8_error
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use alloc_wg::string::String;
/// # use alloc_wg::vec;
/// // some invalid bytes, in a vector
/// let bytes = vec![0, 159];
///
/// let value = String::from_utf8(bytes);
///
/// assert!(value.is_err());
/// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
/// ```
#[derive(Debug)]
pub struct FromUtf8Error<A: DeallocRef = AbortAlloc<Global>> {
    bytes: Vec<u8, A>,
    error: Utf8Error,
}

/// A possible error value when converting a `String` from a UTF-16 byte slice.
///
/// This type is the error type for the [`from_utf16`] method on [`String`].
///
/// [`from_utf16`]: struct.String.html#method.from_utf16
/// [`String`]: struct.String.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use alloc_wg::string::String;
/// // 𝄞mu<invalid>ic
/// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0xD800, 0x0069, 0x0063];
///
/// assert!(String::from_utf16(v).is_err());
/// ```
#[derive(Debug)]
pub struct FromUtf16Error(());

impl String {
    /// Creates a new empty `String`.
    ///
    /// Given that the `String` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: #method.with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```unused_variables
    /// # use alloc_wg::string::String;
    /// let s = String::new();
    /// ```
    #[inline]
    pub const fn new() -> String {
        String { vec: Vec::new() }
    }

    /// Creates a new empty `String` with a particular capacity.
    ///
    /// `String`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `String`, but one with an initial
    /// buffer that can hold `capacity` bytes. This is useful when you may be
    /// appending a bunch of data to the `String`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: #method.capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: #method.new
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::with_capacity(10);
    ///
    /// // The String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for _ in 0..10 {
    ///     s.push('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the vector reallocate
    /// s.push('a');
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> String {
        Self::with_capacity_in(capacity, AbortAlloc(Global))
    }

    /// Decode a UTF-16 encoded vector `v` into a `String`, returning [`Err`]
    /// if `v` contains any invalid data.
    ///
    /// [`Err`]: ../../std/result/enum.Result.html#variant.Err
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0x0069, 0x0063];
    /// assert_eq!(String::from("𝄞music"), String::from_utf16(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0xD800, 0x0069, 0x0063];
    /// assert!(String::from_utf16(v).is_err());
    /// ```
    pub fn from_utf16(v: &[u16]) -> Result<String, FromUtf16Error> {
        Self::from_utf16_in(v, AbortAlloc(Global))
    }

    /// Decode a UTF-16 encoded slice `v` into a `String`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, str>`],
    /// `from_utf16_lossy` returns a `String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: #method.from_utf8_lossy
    /// [`Cow<'a, str>`]: ../borrow/enum.Cow.html
    /// [U+FFFD]: ../char/constant.REPLACEMENT_CHARACTER.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[
    ///     0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834,
    /// ];
    ///
    /// assert_eq!(
    ///     String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///     String::from_utf16_lossy(v)
    /// );
    /// ```
    #[inline]
    pub fn from_utf16_lossy(v: &[u16]) -> String {
        decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .collect()
    }

    /// Creates a new `String` from a length, capacity, and pointer.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * The memory at `ptr` needs to have been previously allocated by the
    ///   same allocator the standard library uses.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `String` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// use std::mem;
    ///
    /// unsafe {
    ///     let s = String::from("hello");
    // FIXME Update this when vec_into_raw_parts is stabilized
    ///     // Prevent automatically dropping the String's data
    ///     let mut s = mem::ManuallyDrop::new(s);
    ///
    ///     let ptr = s.as_mut_ptr();
    ///     let len = s.len();
    ///     let capacity = s.capacity();
    ///
    ///     let s = String::from_raw_parts(ptr, len, capacity);
    ///
    ///     assert_eq!(String::from("hello"), s);
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw_parts(buf: *mut u8, length: usize, capacity: usize) -> String {
        Self::from_raw_parts_in(buf, length, capacity, AbortAlloc(Global))
    }
}

impl<A: DeallocRef> String<A> {
    /// Like `new` but parameterized over the choice of allocator for the returned `Vec`.
    #[inline]
    pub fn new_in(a: A) -> Self {
        String {
            vec: Vec::new_in(a),
        }
    }

    /// Like `with_capacity` but parameterized over the choice of allocator for the returned `Vec`.
    ///
    /// # Panics
    /// Panics if the allocation fails.
    #[inline]
    pub fn with_capacity_in(capacity: usize, a: A) -> Self
    where
        A: AllocRef<Error = crate::Never>,
    {
        String {
            vec: Vec::with_capacity_in(capacity, a),
        }
    }

    /// Like `with_capacity_in` but returns errors instead of panicking.
    #[inline]
    pub fn try_with_capacity_in(capacity: usize, a: A) -> Result<Self, CollectionAllocErr<A>>
    where
        A: AllocRef,
    {
        Ok(String {
            vec: Vec::try_with_capacity_in(capacity, a)?,
        })
    }

    /// Like `from_str` but parameterized over the choice of allocator for the returned `Vec`.
    ///
    /// # Panics
    /// Panics if the allocation fails.
    #[inline]
    pub fn from_str_in(s: &str, a: A) -> Self
    where
        A: ReallocRef<Error = crate::Never>,
    {
        let mut v = String::with_capacity_in(s.len(), a);
        v.push_str(s);
        v
    }

    /// Like `from_str_in` but returns errors instead of panicking.
    #[inline]
    pub fn try_from_str_in(s: &str, a: A) -> Result<Self, CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let mut v = String::try_with_capacity_in(s.len(), a)?;
        v.try_push_str(s)?;
        Ok(v)
    }

    /// Converts a vector of bytes to a `String`.
    ///
    /// A string ([`String`]) is made of bytes ([`u8`]), and a vector of bytes
    /// ([`Vec<u8>`]) is made of bytes, so this function converts between the
    /// two. Not all byte slices are valid `String`s, however: `String`
    /// requires that it is valid UTF-8. `from_utf8()` checks to ensure that
    /// the bytes are valid UTF-8, and then does the conversion.
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// This method will take care to not copy the vector, for efficiency's
    /// sake.
    ///
    /// If you need a [`&str`] instead of a `String`, consider
    /// [`str::from_utf8`].
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why the
    /// provided bytes are not UTF-8. The vector you moved in is also included.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// // We know these bytes are valid, so we'll use `unwrap()`.
    /// let sparkle_heart = String::from_utf8(sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = vec![0, 159, 146, 150];
    ///
    /// assert!(String::from_utf8(sparkle_heart).is_err());
    /// ```
    ///
    /// See the docs for [`FromUtf8Error`] for more details on what you can do
    /// with this error.
    ///
    /// [`from_utf8_unchecked`]: struct.String.html#method.from_utf8_unchecked
    /// [`String`]: struct.String.html
    /// [`u8`]: ../../std/primitive.u8.html
    /// [`Vec<u8>`]: ../../std/vec/struct.Vec.html
    /// [`str::from_utf8`]: ../../std/str/fn.from_utf8.html
    /// [`into_bytes`]: struct.String.html#method.into_bytes
    /// [`FromUtf8Error`]: struct.FromUtf8Error.html
    /// [`Err`]: ../../std/result/enum.Result.html#variant.Err
    #[inline]
    pub fn from_utf8(vec: Vec<u8, A>) -> Result<Self, FromUtf8Error<A>> {
        match str::from_utf8(&vec) {
            Ok(..) => Ok(String { vec }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    /// Like `from_utf8_lossy` but parameterized over the choice of allocator for the returned `Vec`.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails.
    pub fn from_utf8_lossy_in(v: &[u8], a: A) -> Self
    where
        A: ReallocRef<Error = crate::Never>,
    {
        match Self::try_from_utf8_lossy_in(v, a) {
            Ok(s) => s,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { .. }) => unreachable!("Infallible allocation"),
        }
    }

    /// Like `from_utf8_lossy_in` but returns errors instead of panicking.
    pub fn try_from_utf8_lossy_in(v: &[u8], a: A) -> Result<Self, CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let mut iter = lossy::Utf8Lossy::from_bytes(v).chunks();

        let (first_valid, first_broken) = if let Some(chunk) = iter.next() {
            let lossy::Utf8LossyChunk { valid, broken } = chunk;
            if valid.len() == v.len() {
                debug_assert!(broken.is_empty());
                return String::try_from_str_in(valid, a);
            }
            (valid, broken)
        } else {
            return Ok(String::new_in(a));
        };

        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = String::try_with_capacity_in(v.len(), a)?;
        res.try_push_str(first_valid)?;
        if !first_broken.is_empty() {
            res.try_push_str(REPLACEMENT)?;
        }

        for lossy::Utf8LossyChunk { valid, broken } in iter {
            res.try_push_str(valid)?;
            if !broken.is_empty() {
                res.try_push_str(REPLACEMENT)?;
            }
        }

        Ok(res)
    }

    /// Like `from_utf16` but parameterized over the choice of allocator for the returned `Vec`.
    pub fn from_utf16_in(v: &[u16], a: A) -> Result<Self, FromUtf16Error>
    where
        A: ReallocRef<Error = crate::Never>,
    {
        // This isn't done via collect::<Result<_, _>>() for performance reasons.
        // FIXME: the function can be simplified again when #48994 is closed.
        let mut ret = String::with_capacity_in(v.len(), a);
        for c in decode_utf16(v.iter().cloned()) {
            if let Ok(c) = c {
                ret.push(c);
            } else {
                return Err(FromUtf16Error(()));
            }
        }
        Ok(ret)
    }

    /// Decomposes a `String` into its raw components.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the string (in bytes), and the allocated capacity of the data
    /// (in bytes). These are the same arguments in the same order as
    /// the arguments to [`from_raw_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `String`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `String` with the [`from_raw_parts`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_raw_parts`]: #method.from_raw_parts
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s = String::from("hello");
    ///
    /// let (ptr, len, cap) = s.into_raw_parts();
    ///
    /// let rebuilt = unsafe { String::from_raw_parts(ptr, len, cap) };
    /// assert_eq!(rebuilt, "hello");
    /// ```
    pub fn into_raw_parts(self) -> (*mut u8, usize, usize) {
        self.vec.into_raw_parts()
    }

    /// Like `from_raw_parts` but parameterized over the choice of allocator for the returned `Vec`.
    #[inline]
    pub unsafe fn from_raw_parts_in(
        buf: *mut u8,
        length: usize,
        capacity: usize,
        b: A::BuildAlloc,
    ) -> Self {
        String {
            vec: Vec::from_raw_parts_in(buf, length, capacity, b),
        }
    }

    /// Converts a vector of bytes to a `String` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more details.
    ///
    /// [`from_utf8`]: struct.String.html#method.from_utf8
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the standard library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe { String::from_utf8_unchecked(sparkle_heart) };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8, A>) -> Self {
        String { vec: bytes }
    }

    /// Converts a `String` into a byte vector.
    ///
    /// This consumes the `String`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s = String::from("hello");
    /// let bytes = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, A> {
        self.vec
    }

    /// Extracts a string slice containing the entire `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s = String::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        self
    }

    /// Converts a `String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    ///
    /// # Panics
    /// Panics if the reallocation fails.
    #[inline]
    pub fn push_str(&mut self, string: &str)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        self.vec.extend_from_slice(string.as_bytes())
    }

    /// Like `push_str` but returns errors instead of panicking.
    #[inline]
    pub fn try_push_str(&mut self, string: &str) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.vec.try_extend_from_slice(string.as_bytes())
    }

    /// Returns this `String`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s = String::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Ensures that this `String`'s capacity is at least `additional` bytes
    /// larger than its length.
    ///
    /// The capacity may be increased by more than `additional` bytes if it
    /// chooses, to prevent frequent reallocations.
    ///
    /// If you do not want this "at least" behavior, see the [`reserve_exact`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// [`reserve_exact`]: struct.String.html#method.reserve_exact
    /// [`usize`]: ../../std/primitive.usize.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::new();
    ///
    /// s.reserve(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This may not actually increase the capacity:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        self.vec.reserve(additional)
    }

    /// Ensures that this `String`'s capacity is `additional` bytes
    /// larger than its length.
    ///
    /// Consider using the [`reserve`] method unless you absolutely know
    /// better than the allocator.
    ///
    /// [`reserve`]: #method.reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::new();
    ///
    /// s.reserve_exact(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This may not actually increase the capacity:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve_exact(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        self.vec.reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `String`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{
    ///     alloc::{AbortAlloc, Global},
    ///     collections::CollectionAllocErr,
    ///     string::String,
    /// };
    ///
    /// fn process_data(data: &str) -> Result<String, CollectionAllocErr<AbortAlloc<Global>>> {
    ///     let mut output = String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `String`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use alloc_wg::{
    ///     alloc::{AbortAlloc, Global},
    ///     collections::CollectionAllocErr,
    ///     string::String,
    /// };
    ///
    /// fn process_data(data: &str) -> Result<String, CollectionAllocErr<AbortAlloc<Global>>> {
    ///     let mut output = String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.vec.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `String` to match its length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    ///
    /// # Panics
    /// Panics if the reallocation fails
    #[inline]
    pub fn shrink_to_fit(&mut self)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        self.vec.shrink_to_fit()
    }

    /// Like `shrink_to_fit` but returns errors instead of panicking.
    #[inline]
    pub fn try_shrink_to_fit(&mut self) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.vec.try_shrink_to_fit()
    }

    /// Shrinks the capacity of this `String` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// Panics if the current capacity is smaller than the supplied
    /// minimum capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to(10);
    /// assert!(s.capacity() >= 10);
    /// s.shrink_to(0);
    /// assert!(s.capacity() >= 3);
    /// ```
    ///
    /// # Panics
    /// * Panics if the given amount is *larger* than the current capacity.
    /// * Panics if the reallocation fails.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        self.vec.shrink_to(min_capacity)
    }

    /// Like `shrink_to` but returns errors instead of panicking.
    #[inline]
    pub fn try_shrink_to(&mut self, min_capacity: usize) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        self.vec.try_shrink_to(min_capacity)
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    ///
    /// # Panics
    /// Panics if the reallocation fails.
    #[inline]
    pub fn push(&mut self, ch: char)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        match self.try_push(ch) {
            Ok(s) => s,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { .. }) => unreachable!("Infallible allocation"),
        }
    }

    /// Like `push` but returns errors instead of panicking.
    #[inline]
    pub fn try_push(&mut self, ch: char) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        match ch.len_utf8() {
            1 => self.vec.try_push(ch as u8),
            _ => self
                .vec
                .try_extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    /// Returns a byte slice of this `String`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: #method.from_utf8
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s = String::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `String` is empty.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(newlen);
        }
        Some(ch)
    }

    /// Removes a [`char`] from this `String` at a byte position and returns it.
    ///
    /// This is an `O(n)` operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(next),
                self.vec.as_mut_ptr().add(idx),
                len - next,
            );
            self.vec.set_len(len - (next - idx));
        }
        ch
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, "foobar");
    /// ```
    ///
    /// The exact order may be useful for tracking external state, like an index.
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("abcde");
    /// let keep = [false, true, true, false, true];
    /// let mut i = 0;
    /// s.retain(|_| (keep[i], i += 1).0);
    /// assert_eq!(s, "bce");
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        while idx < len {
            let ch = unsafe { self.get_unchecked(idx..len).chars().next().unwrap() };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    ptr::copy(
                        self.vec.as_ptr().add(idx),
                        self.vec.as_mut_ptr().add(idx - del_bytes),
                        ch_len,
                    );
                }
            }

            // Point idx to the next char
            idx += ch_len;
        }

        if del_bytes > 0 {
            unsafe {
                self.vec.set_len(len - del_bytes);
            }
        }
    }

    /// Inserts a character into this `String` at a byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    ///
    /// # Panics
    /// Panics if reallocation fails.
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        match self.try_insert(idx, ch) {
            Ok(s) => s,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { .. }) => unreachable!("Infallible allocation"),
        }
    }

    /// Like `insert` but returns errors instead of panicking.
    #[inline]
    pub fn try_insert(&mut self, idx: usize, ch: char) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();

        unsafe { self.try_insert_bytes(idx, bits) }
    }

    unsafe fn try_insert_bytes(
        &mut self,
        idx: usize,
        bytes: &[u8],
    ) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let len = self.len();
        let amt = bytes.len();
        self.vec.try_reserve(amt)?;

        ptr::copy(
            self.vec.as_ptr().add(idx),
            self.vec.as_mut_ptr().add(idx + amt),
            len - idx,
        );
        ptr::copy(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        self.vec.set_len(len + amt);
        Ok(())
    }

    /// Inserts a string slice into this `String` at a byte position.
    ///
    /// This is an `O(n)` operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    ///
    /// # Panics
    /// Panics if the reallocation fails.
    #[inline]
    pub fn insert_str(&mut self, idx: usize, string: &str)
    where
        A: ReallocRef<Error = crate::Never>,
    {
        match self.try_insert_str(idx, string) {
            Ok(s) => s,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { .. }) => unreachable!("Infallible allocation"),
        }
    }

    /// Like `insert_str` but returns errors instead of panicking.
    #[inline]
    pub fn try_insert_str(&mut self, idx: usize, string: &str) -> Result<(), CollectionAllocErr<A>>
    where
        A: ReallocRef<Error = crate::Never>,
    {
        assert!(self.is_char_boundary(idx));

        unsafe { self.try_insert_bytes(idx, string.as_bytes()) }
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the standard library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8, A> {
        &mut self.vec
    }

    /// Returns the length of this `String`, in bytes, not [`char`]s or
    /// graphemes. In other words, it may not be what a human considers the
    /// length of the string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let a = String::from("foo");
    /// assert_eq!(a.len(), 3);
    ///
    /// let fancy_f = String::from("ƒoo");
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `String` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut v = String::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut hello = String::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// ```
    ///
    /// # Panics
    /// Panics if the allocation fails.
    #[inline]
    pub fn split_off(&mut self, at: usize) -> Self
    where
        A: AllocRef<Error = crate::Never>,
    {
        match self.try_split_off(at) {
            Ok(s) => s,
            Err(CollectionAllocErr::CapacityOverflow) => capacity_overflow(),
            Err(CollectionAllocErr::AllocError { .. }) => unreachable!("Infallible allocation"),
        }
    }

    /// Like `split_off` but returns errors instead of panicking.
    #[inline]
    pub fn try_split_off(&mut self, at: usize) -> Result<Self, CollectionAllocErr<A>>
    where
        A: AllocRef,
    {
        assert!(self.is_char_boundary(at));
        let other = self.vec.try_split_off(at)?;
        unsafe { Ok(String::from_utf8_unchecked(other)) }
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    /// Creates a draining iterator that removes the specified range in the `String`
    /// and yields the removed `chars`.
    ///
    /// Note: The element range is removed even if the iterator is not
    /// consumed until the end.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Remove the range up until the β from the string
    /// let t: String = s.drain(..beta_offset).collect();
    /// assert_eq!(t, "α is alpha, ");
    /// assert_eq!(s, "β is beta");
    ///
    /// // A full range clears the string
    /// s.drain(..);
    /// assert_eq!(s, "");
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, A>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // The String version of Drain does not have the memory safety issues
        // of the vector version. The data is just plain bytes.
        // Because the range removal happens in Drop, if the Drain iterator is leaked,
        // the removal will not happen.
        let len = self.len();
        let start = match range.start_bound() {
            Included(&n) => n,
            Excluded(&n) => n + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&n) => n + 1,
            Excluded(&n) => n,
            Unbounded => len,
        };

        // Take out two simultaneous borrows. The &mut String won't be accessed
        // until iteration is over, in Drop.
        let self_ptr: *mut Self = self;
        // slicing does the appropriate bounds checks
        let chars_iter = self[start..end].chars();

        Drain {
            start,
            end,
            iter: chars_iter,
            string: self_ptr,
        }
    }

    /// Removes the specified range in the string,
    /// and replaces it with the given string.
    /// The given string doesn't need to be the same length as the range.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// [`char`]: ../../std/primitive.char.html
    /// [`Vec::splice`]: ../../std/vec/struct.Vec.html#method.splice
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let mut s = String::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Replace the range up until the β from the string
    /// s.replace_range(..beta_offset, "Α is capital alpha; ");
    /// assert_eq!(s, "Α is capital alpha; β is beta");
    /// ```
    pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
    where
        R: RangeBounds<usize>,
        A: ReallocRef<Error = crate::Never>,
    {
        // Memory safety
        //
        // Replace_range does not have the memory safety issues of a vector Splice.
        // of the vector version. The data is just plain bytes.

        match range.start_bound() {
            Included(&n) => assert!(self.is_char_boundary(n)),
            Excluded(&n) => assert!(self.is_char_boundary(n + 1)),
            Unbounded => {}
        };
        match range.end_bound() {
            Included(&n) => assert!(self.is_char_boundary(n + 1)),
            Excluded(&n) => assert!(self.is_char_boundary(n)),
            Unbounded => {}
        };

        unsafe { self.as_mut_vec() }.splice(range, replace_with.bytes());
    }

    /// Converts this `String` into a [`Box`]`<`[`str`]`>`.
    ///
    /// This will drop any excess capacity.
    ///
    /// [`Box`]: ../../std/boxed/struct.Box.html
    /// [`str`]: ../../std/primitive.str.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```unused_variables
    /// # use alloc_wg::string::String;
    /// let s = String::from("hello");
    ///
    /// let b = s.into_boxed_str();
    /// ```
    ///
    /// # Panics
    /// Panics if the reallocation fails.
    #[inline]
    pub fn into_boxed_str(self) -> Box<str, A>
    where
        A: ReallocRef<Error = crate::Never>,
    {
        let slice = self.vec.into_boxed_slice();
        unsafe { from_boxed_utf8_unchecked(slice) }
    }

    /// Like `into_boxed_str` but returns errors instead of panicking.
    #[inline]
    pub fn try_into_boxed_str(self) -> Result<Box<str, A>, CollectionAllocErr<A>>
    where
        A: ReallocRef,
    {
        let slice = self.vec.try_into_boxed_slice()?;
        unsafe { Ok(from_boxed_utf8_unchecked(slice)) }
    }
}

impl<A: DeallocRef> FromUtf8Error<A> {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a `String`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = String::from_utf8(bytes);
    ///
    /// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
    /// ```
    pub fn into_bytes(self) -> Vec<u8, A> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`Utf8Error`]: ../../std/str/struct.Utf8Error.html
    /// [`std::str`]: ../../std/str/index.html
    /// [`u8`]: ../../std/primitive.u8.html
    /// [`&str`]: ../../std/primitive.str.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec;
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let error = String::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<A: DeallocRef> fmt::Display for FromUtf8Error<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

impl Clone for String {
    fn clone(&self) -> Self {
        String {
            vec: self.vec.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}

impl FromIterator<char> for String {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

impl<'a> FromIterator<&'a char> for String {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

impl<'a> FromIterator<&'a str> for String {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> String {
        let mut buf = String::new();
        buf.extend(iter);
        buf
    }
}

impl FromIterator<String> for String {
    fn from_iter<I: IntoIterator<Item = String>>(iter: I) -> String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => String::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<Cow<'a, str>> for String {
    fn from_iter<I: IntoIterator<Item = Cow<'a, str>>>(iter: I) -> String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over CoWs, we can (potentially) avoid at least
        // one allocation by getting the first item and appending to it all the
        // subsequent items.
        match iterator.next() {
            None => String::new(),
            Some(cow) => {
                let mut buf = String::from(&cow[..]);
                buf.extend(iterator);
                buf
            }
        }
    }
}

impl<A> Extend<char> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }
}

impl<A: ReallocRef> TryExtend<char> for String<A> {
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = char>>(&mut self, iter: I) -> Result<(), Self::Err> {
        let mut iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.try_reserve(lower_bound)?;
        iterator.try_for_each(move |c| self.try_push(c))?;
        Ok(())
    }
}

impl<'a, A> Extend<&'a char> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<'a, A: ReallocRef> TryExtend<&'a char> for String<A> {
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) -> Result<(), Self::Err> {
        self.try_extend(iter.into_iter().cloned())
    }
}

impl<'a, A> Extend<&'a str> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }
}

impl<'a, A: ReallocRef> TryExtend<&'a str> for String<A> {
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) -> Result<(), Self::Err> {
        iter.into_iter().try_for_each(move |s| self.try_push_str(s))
    }
}

impl<A, B> Extend<String<B>> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
    B: DeallocRef,
{
    fn extend<I: IntoIterator<Item = String<B>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

impl<A: ReallocRef, B: DeallocRef> TryExtend<String<B>> for String<A> {
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = String<B>>>(&mut self, iter: I) -> Result<(), Self::Err> {
        iter.into_iter()
            .try_for_each(move |s| self.try_push_str(&s))
    }
}

#[cfg(feature = "std")]
impl<'a, A> Extend<Cow<'a, str>> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

#[cfg(feature = "std")]
impl<'a, A: ReallocRef> TryExtend<Cow<'a, str>> for String<A> {
    type Err = CollectionAllocErr<A>;

    fn try_extend<I: IntoIterator<Item = Cow<'a, str>>>(
        &mut self,
        iter: I,
    ) -> Result<(), Self::Err> {
        iter.into_iter()
            .try_for_each(move |s| self.try_push_str(&s))
    }
}

impl<A: DeallocRef, B: DeallocRef> PartialEq<String<B>> for String<A> {
    #[inline]
    fn eq(&self, other: &String<B>) -> bool {
        PartialEq::eq(&self[..], &other[..])
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs:ty) => {
        #[allow(unused_lifetimes)]
        impl<A: DeallocRef> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
        }

        #[allow(unused_lifetimes)]
        impl<A: DeallocRef> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
        }
    };
}

impl_eq! { String<A>, str }
impl_eq! { String<A>, &'_ str }

#[cfg(feature = "std")]
mod borrow {
    use super::String;
    use crate::alloc::DeallocRef;
    use std::borrow::Cow;

    impl_eq! { Cow<'_, str>, String<A> }
    impl_eq! { String<A>, std::string::String }
}

impl Default for String {
    /// Creates an empty `String`.
    #[inline]
    fn default() -> Self {
        String::new()
    }
}

impl<A: DeallocRef> fmt::Display for String<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<A: DeallocRef> fmt::Debug for String<A> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<A: DeallocRef> hash::Hash for String<A> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `String` on the left-hand side and re-uses its buffer (growing it if
/// necessary). This is done to avoid allocating a new `String` and copying the entire contents on
/// every operation, which would lead to `O(n^2)` running time when building an `n`-byte string by
/// repeated concatenation.
///
/// The string on the right-hand side is only borrowed; its contents are copied into the returned
/// `String`.
///
/// # Examples
///
/// Concatenating two `String`s takes the first by value and borrows the second:
///
/// ```unused_variables
/// # use alloc_wg::string::String;
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a + &b;
/// // `a` is moved and can no longer be used here.
/// ```
///
/// If you want to keep using the first `String`, you can clone it and append to the clone instead:
///
/// ```unused_variables
/// # use alloc_wg::string::String;
/// let a = String::from("hello");
/// let b = String::from(" world");
/// let c = a.clone() + &b;
/// // `a` is still valid here.
/// ```
///
/// Concatenating `&str` slices can be done by converting the first to a `String`:
///
/// ```unused_variables
/// # use alloc_wg::string::ToString;
/// let a = "hello";
/// let b = " world";
/// let c = String::from(a) + b;
/// ```
impl<A> Add<&str> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    type Output = Self;

    #[inline]
    fn add(mut self, other: &str) -> Self {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `String`.
///
/// This has the same behavior as the [`push_str`][String::push_str] method.
impl<A> AddAssign<&str> for String<A>
where
    A: ReallocRef<Error = crate::Never>,
{
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

impl<A: DeallocRef> Index<ops::Range<usize>> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &str {
        &self[..][index]
    }
}
impl<A: DeallocRef> Index<ops::RangeTo<usize>> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &str {
        &self[..][index]
    }
}
impl<A: DeallocRef> Index<ops::RangeFrom<usize>> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &str {
        &self[..][index]
    }
}
impl<A: DeallocRef> Index<ops::RangeFull> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}
impl<A: DeallocRef> Index<ops::RangeInclusive<usize>> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}
impl<A: DeallocRef> Index<ops::RangeToInclusive<usize>> for String<A> {
    type Output = str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
        Index::index(&**self, index)
    }
}

impl<A: DeallocRef> IndexMut<ops::Range<usize>> for String<A> {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
        &mut self[..][index]
    }
}
impl<A: DeallocRef> IndexMut<ops::RangeTo<usize>> for String<A> {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
        &mut self[..][index]
    }
}
impl<A: DeallocRef> IndexMut<ops::RangeFrom<usize>> for String<A> {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
        &mut self[..][index]
    }
}
impl<A: DeallocRef> IndexMut<ops::RangeFull> for String<A> {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}
impl<A: DeallocRef> IndexMut<ops::RangeInclusive<usize>> for String<A> {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}
impl<A: DeallocRef> IndexMut<ops::RangeToInclusive<usize>> for String<A> {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
        IndexMut::index_mut(&mut **self, index)
    }
}

impl<A: DeallocRef> ops::Deref for String<A> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.vec) }
    }
}

impl<A: DeallocRef> ops::DerefMut for String<A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}

/// An error when parsing a `String`.
///
/// This `enum` is slightly awkward: it will never actually exist. This error is
/// part of the type signature of the implementation of [`FromStr`] on
/// [`String`]. The return type of [`from_str`], requires that an error be
/// defined, but, given that a [`String`] can always be made into a new
/// [`String`] without error, this type will never actually be returned. As
/// such, it is only here to satisfy said signature, and is useless otherwise.
///
/// [`FromStr`]: ../../std/str/trait.FromStr.html
/// [`String`]: struct.String.html
/// [`from_str`]: ../../std/str/trait.FromStr.html#tymethod.from_str
pub type ParseError = core::convert::Infallible;

impl FromStr for String {
    type Err = core::convert::Infallible;
    #[inline]
    fn from_str(s: &str) -> Result<String, ParseError> {
        Ok(String::from(s))
    }
}

/// A trait for converting a value to a `String`.
///
/// This trait is automatically implemented for any type which implements the
/// [`Display`] trait. As such, `ToString` shouldn't be implemented directly:
/// [`Display`] should be implemented instead, and you get the `ToString`
/// implementation for free.
///
/// [`Display`]: ../../std/fmt/trait.Display.html
pub trait ToString {
    /// Converts the given value to a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let i = 5;
    /// let five = String::from("5");
    ///
    /// assert_eq!(five, i.to_string());
    /// ```
    fn to_string(&self) -> String;
}

/// # Panics
///
/// In this implementation, the `to_string` method panics
/// if the `Display` implementation returns an error.
/// This indicates an incorrect `Display` implementation
/// since `fmt::Write for String` never returns an error itself.

impl<T: fmt::Display + ?Sized> ToString for T {
    #[inline]
    fn to_string(&self) -> String {
        use fmt::Write;
        let mut buf = String::new();
        buf.write_fmt(format_args!("{}", self))
            .expect("a Display implementation returned an error unexpectedly");
        buf.shrink_to_fit();
        buf
    }
}

impl<A: DeallocRef> AsRef<str> for String<A> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<A: DeallocRef> AsRef<[u8]> for String<A> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl From<&str> for String {
    #[inline]
    fn from(s: &str) -> String {
        let mut v = String::new();
        v.push_str(s);
        v
    }
}

impl From<&String> for String {
    #[inline]
    fn from(s: &String) -> String {
        s.clone()
    }
}

// note: test pulls in libstd, which causes errors here
#[cfg(not(test))]
impl From<Box<str>> for String {
    /// Converts the given boxed `str` slice to a `String`.
    /// It is notable that the `str` slice is owned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// let s1: String = String::from("hello world");
    /// let s2 = s1.into_boxed_str();
    /// let s3: String = String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: Box<str>) -> String {
        String::from(&s[..])
    }
}

impl<A> From<String<A>> for Box<str, A>
where
    A: ReallocRef<Error = crate::Never>,
{
    /// Converts the given `String` to a boxed `str` slice that is owned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::boxed::Box;
    /// let s1: String = String::from("hello world");
    /// let s2: Box<str> = Box::from(s1);
    /// let s3: String = String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: String<A>) -> Self {
        s.into_boxed_str()
    }
}

#[cfg(feature = "std")]
impl<'a> From<Cow<'a, str>> for String {
    fn from(s: Cow<'a, str>) -> String {
        String::from(&s[..])
    }
}

#[cfg(feature = "std")]
impl<'a, A: DeallocRef> From<&'a String<A>> for Cow<'a, str> {
    #[inline]
    fn from(s: &'a String<A>) -> Cow<'a, str> {
        Cow::Borrowed(s.as_str())
    }
}

impl<A: DeallocRef> From<String<A>> for Vec<u8, A> {
    /// Converts the given `String` to a vector `Vec` that holds values of type `u8`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use alloc_wg::string::String;
    /// # use alloc_wg::vec::Vec;
    /// let s1 = String::from("hello world");
    /// let v1 = Vec::from(s1);
    ///
    /// for b in v1 {
    ///     println!("{}", b);
    /// }
    /// ```
    fn from(string: String<A>) -> Self {
        string.into_bytes()
    }
}

impl<A: ReallocRef> fmt::Write for String<A> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.try_push(c).map_err(|_| fmt::Error)
    }
}

/// A draining iterator for `String`.
///
/// This struct is created by the [`drain`] method on [`String`]. See its
/// documentation for more.
///
/// [`drain`]: struct.String.html#method.drain
/// [`String`]: struct.String.html
pub struct Drain<'a, A: DeallocRef> {
    /// Will be used as &'a mut String in the destructor
    string: *mut String<A>,
    /// Start of part to remove
    start: usize,
    /// End of part to remove
    end: usize,
    /// Current remaining range to remove
    iter: Chars<'a>,
}

impl<A: DeallocRef> fmt::Debug for Drain<'_, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Drain { .. }")
    }
}

unsafe impl<A: DeallocRef> Sync for Drain<'_, A> {}
unsafe impl<A: DeallocRef> Send for Drain<'_, A> {}

impl<A: DeallocRef> Drop for Drain<'_, A> {
    fn drop(&mut self) {
        unsafe {
            // Use Vec::drain. "Reaffirm" the bounds checks to avoid
            // panic code being inserted again.
            let self_vec = (*self.string).as_mut_vec();
            if self.start <= self.end && self.end <= self_vec.len() {
                self_vec.drain(self.start..self.end);
            }
        }
    }
}

impl<A: DeallocRef> Iterator for Drain<'_, A> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl<A: DeallocRef> DoubleEndedIterator for Drain<'_, A> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl<A: DeallocRef> FusedIterator for Drain<'_, A> {}

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}
