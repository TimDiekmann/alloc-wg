# v0.7

- Add `Vec`

# v0.6

- Provide default implementation for `realloc`
- Don't reexport `Layout`
- Make `NonZeroLayout::size`, `padding_needed_for` and `align` const

# v0.5

- Add `usable_size`, `grow_in_place`, and `shrink_in_place` to `AllocRef`
- Add `(try_)reserve_in_place` and `(try_)double(_in_place)` for `RawVec`
- Add `CloneIn` trait for `Box`
- Use `AbortAlloc<Global>` as default for `RawVec` instead of `Global`
- Use `NonZeroUsize` in `NonZeroLayout`
- Add `#[must_use]` as proposed by clippy

# v0.4

- Add `RawVec<T, B: BuildAlloc>`
- Rename `BuildAlloc` to `BuildAllocRef`
- Use `Option<NonZeroLayout>` for `BuildAllocRef`

# v0.3

- Change methods for retrieving `B` and allocator in `Box<T, B>`
- Unify all builder traits into `BuildAlloc`

# v0.2

- Add `Box<T, B: BuildDealloc>`

# v0.1

- Initial release