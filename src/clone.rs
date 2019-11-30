use crate::alloc::{AllocRef, Panic};

pub trait CloneIn<A: AllocRef>: Sized {
    type Cloned;

    fn clone_in(&self, a: A) -> Self::Cloned
    where
        A: AllocRef<Error = Panic>;

    fn try_clone_in(&self, a: A) -> Result<Self::Cloned, A::Error>;
}
