#![allow(explicit_outlives_requirements, single_use_lifetimes, trivial_casts)]
#![allow(clippy::pedantic, clippy::nursery, clippy::type_complexity)]
#![deny(unsafe_op_in_unsafe_fn)]
mod borrow;
pub mod map;
mod navigate;
mod node;
mod search;
pub mod set;
#[cfg(all(test, std))]
mod tests;

#[doc(hidden)]
trait Recover<Q: ?Sized> {
    type Key;

    fn get(&self, key: &Q) -> Option<&Self::Key>;
    fn take(&mut self, key: &Q) -> Option<Self::Key>;
    fn replace(&mut self, key: Self::Key) -> Option<Self::Key>;
}

#[inline(always)]
pub unsafe fn unwrap_unchecked<T>(val: Option<T>) -> T {
    val.unwrap_or_else(|| {
        if cfg!(debug_assertions) {
            panic!("'unchecked' unwrap on None in BTreeMap");
        } else {
            unsafe {
                core::intrinsics::unreachable();
            }
        }
    })
}
