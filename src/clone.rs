use crate::alloc::BuildAllocRef;

pub trait CloneIn<A: BuildAllocRef>: Sized {
    type Cloned;

    fn clone_in(&self, a: A) -> Self::Cloned;
}
