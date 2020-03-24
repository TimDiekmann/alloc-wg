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
