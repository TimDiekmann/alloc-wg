Alloc-WG
========


[![Test Status](https://github.com/TimDiekmann/alloc-wg/workflows/Test/badge.svg?event=push&branch=master)](https://github.com/TimDiekmann/alloc-wg/actions?query=workflow%3ATest+event%3Apush+branch%3Amaster)
[![Lint Status](https://github.com/TimDiekmann/alloc-wg/workflows/Lint/badge.svg?event=push&branch=master)](https://github.com/TimDiekmann/alloc-wg/actions?query=workflow%3ALint+event%3Apush+branch%3Amaster)
[![Docs master](https://img.shields.io/static/v1?label=docs&message=master&color=5479ab)](https://timdiekmann.github.io/alloc-wg/alloc_wg/index.html)
[![Docs.rs](https://docs.rs/alloc-wg/badge.svg)](https://docs.rs/alloc-wg)
[![Crates.io](https://img.shields.io/crates/v/alloc-wg)](https://crates.io/crates/alloc-wg)
![Crates.io](https://img.shields.io/crates/l/alloc-wg)

An attempt to collect several proposals of [rust-lang/wg-allocators](https://github.com/rust-lang/wg-allocators) into a
MVP.

**This crate is WIP**, requires a nightly compiler, and is designed to replace the alloc crate. However, this is not completely possible as crate, as some 
compiler features are not possible for crates.

Changes regarding the current `Alloc` trait
-------------------------------------------

- The first thing to notice is, that [`Alloc`] was renamed to [`AllocRef`] in order to show that they are typically 
  implemented for a reference or smart pointer or ZST, not directly for the type that actually holds the allocator’s 
  state.

  Issue: [rust-lang/wg-allocators#8](https://github.com/rust-lang/wg-allocators/issues/8)

- [`AllocRef`] was split up into [`AllocRef`], [`DeallocRef`], and [`ReallocRef`] to make more flexible allocators
  possible. 

  Issue: [rust-lang/wg-allocators#9](https://github.com/rust-lang/wg-allocators/issues/9)

- The allocators has to be associated with [`BuildAllocRef`]. It is related to the allocator traits similar how 
  [`BuildHasher`] is related to [`Hasher`]. Although the signatures are different, it makes an even more flexible 
  allocator design possible.

  Issue: [rust-lang/wg-allocators#12](https://github.com/rust-lang/wg-allocators/issues/12)

- Added an associative error type to [`AllocRef`]. Besides adding the possibility of returning additional information on
  allocation failure, it's also possible to split the usage of the [`AllocRef`] into a fallible and an infallible case.
  Personally I think this is a pretty big deal, as kernel programmer can rely on allocation, which will never fail. If
  an allocation can fail, only a `try_*_in` method may be available. To maintain backwards compatibility, [`AbortAlloc`]
  was introduced. [`AbortAlloc`] wraps another allocator, but aborts on OOM thus `AbortAlloc<Global>` may be used as
  default allocator for [`Box`] or `Vec`. To realize this, [`AbortAlloc`] implements `AllocRef<Error=!>`.

  Issue: [rust-lang/wg-allocators#23](https://github.com/rust-lang/wg-allocators/issues/23)

- The new layout type [`NonZeroLayout`] was introduced. Currently, implementors of [`Alloc`] can chose to allow
  zero-sized allocation so in a generic context it's impossible to rely on this, so banning zero-sized allocation is a
  possible step to prevent this. This also removes `unsafe` from [`AllocRef::alloc`] and [`AllocRef::alloc_zeroed`], and
  unlocks the possibility to move the extension API like `alloc_array` into a separate trait.

  Issue: [rust-lang/wg-allocators#16](https://github.com/rust-lang/wg-allocators/issues/16)

- Support reallocating to a different alignment.

  Issue: [rust-lang/wg-allocators#5](https://github.com/rust-lang/wg-allocators/issues/5)

- Add support for `_zeroed` buffer in `Vec`.

  Issue: [rust-lang/wg-allocators#32](https://github.com/rust-lang/wg-allocators/issues/32)

Currently associated containers
-------------------------------
  
- [`Box`]struct
  - specialization of sized iterators as it's not possible for downstream crates.
  - Limited `T: Copy` for `Fn`-traits as it's not possible for downstream crates.
   
- [`RawVec`]
- [`Vec`]
- [`String`]

[`Alloc`]: https://doc.rust-lang.org/1.38.0/alloc/alloc/trait.Alloc.html
[`AllocRef`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.AllocRef.html
[`AllocRef::alloc`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.AllocRef.html#tymethod.alloc
[`AllocRef::alloc_zeroed`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.AllocRef.html#method.alloc_zeroed
[`Box`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/boxed/struct.Box.html
[`RawVec`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/raw_vec/struct.RawVec.html
[`Vec`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/vec/struct.Vec.html
[`DeallocRef`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.DeallocRef.html
[`ReallocRef`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.ReallocRef.html
[`BuildAllocRef`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/trait.BuildAllocRef.html
[`BuildHasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.BuildHasher.html
[`Hasher`]: https://doc.rust-lang.org/1.38.0/core/hash/trait.Hasher.html
[`NonZeroLayout`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/struct.NonZeroLayout.html
[`AbortAlloc`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/alloc/struct.AbortAlloc.html
[`String`]: https://timdiekmann.github.io/alloc-wg/alloc_wg/string/struct.String.html

License
-------
Alloc-WG is distributed under the terms of both the MIT license and the Apache License (Version 2.0).

See [LICENSE-APACHE](https://github.com/TimDiekmann/alloc-wg/blob/master/LICENSE-APACHE) and [LICENSE-MIT](https://github.com/TimDiekmann/alloc-wg/blob/master/LICENSE-MIT) for details.
