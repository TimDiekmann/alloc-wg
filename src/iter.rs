/// Extend a collection "fallibly" with the contents of an iterator.
pub trait TryExtend<A> {
    type Err;
    /// Extends a collection "fallibly" with the contents of an iterator.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use alloc_wg::{iter::TryExtend, vec};
    ///
    /// // You can extend a Vec<char> with some chars:
    /// let mut message = vec!['a', 'b', 'c'];
    ///
    /// message.try_extend(['d', 'e', 'f'].iter())?;
    ///
    /// assert_eq!(vec!['a', 'b', 'c', 'd', 'e', 'f'], message);
    /// # Ok::<(), alloc_wg::collections::CollectionAllocErr<alloc_wg::alloc::AbortAlloc<alloc_wg::alloc::Global>>>(())
    /// ```
    fn try_extend<T: IntoIterator<Item = A>>(&mut self, iter: T) -> Result<(), Self::Err>;
}
