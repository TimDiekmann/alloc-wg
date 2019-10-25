use crate::alloc::AllocRef;

pub trait CloneIn<A: AllocRef>: Sized {
    type Cloned;

    fn clone_in(&self, a: A) -> Self::Cloned
    where
        A: AllocRef<Error = crate::Never>;

    fn try_clone_in(&self, a: A) -> Result<Self::Cloned, A::Error>;
}
