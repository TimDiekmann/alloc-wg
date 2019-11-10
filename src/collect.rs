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
    /// # use alloc_wg::vec;
    /// use alloc_wg::collect::TryExtend;
    /// // You can extend a Vec<char> with some chars:
    /// let mut message = vec!['a', 'b', 'c'];
    ///
    /// message.try_extend(['d', 'e', 'f'].iter()).unwrap();
    ///
    /// assert_eq!(vec!['a', 'b', 'c', 'd', 'e', 'f'], message);
    /// ```
    fn try_extend<T: IntoIterator<Item = A>>(&mut self, iter: T) -> Result<(), Self::Err>;
}
