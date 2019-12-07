use crate::alloc::{Abort, AllocRef};

pub trait CloneIn<A: AllocRef>: Sized {
    type Cloned;

    fn clone_in(&self, a: A) -> Self::Cloned
    where
        A: Abort;

    fn try_clone_in(&self, a: A) -> Result<Self::Cloned, A::Error>;
}
