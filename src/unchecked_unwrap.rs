use core::hint::unreachable_unchecked;

/// An extension trait for `Option<T>` providing unchecked unwrapping.
pub trait UncheckedOptionExt<T> {
    /// Unwraps an `Option`, yielding the content of a [`Some`][].
    ///
    /// # Safety
    ///
    /// The `Option` has to be `Some`
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::UncheckedOptionExt;
    ///
    /// let x = Some("air");
    /// unsafe {
    ///     assert_eq!(x.unwrap_unchecked(), "air");
    /// }
    /// ```
    unsafe fn unwrap_unchecked(self) -> T;

    /// Unwraps an `Option`, expecting [`None`][] and returning nothing.
    ///
    /// # Safety
    ///
    /// The `Option` has to be `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::UncheckedOptionExt;
    /// use std::collections::HashMap;
    ///
    /// let mut squares = HashMap::new();
    /// for i in -10..=10 {
    ///     unsafe {
    ///         squares.insert(i, i * i).unwrap_none_unchecked();
    ///     }
    /// }
    /// ```
    unsafe fn unwrap_none_unchecked(self);
}

/// An extension trait for `Result<T, E>` providing unchecked unwrapping.
pub trait UncheckedResultExt<T, E> {
    /// Unwraps a `Result`, yielding the content of an [`Ok`][].
    ///
    /// # Safety
    ///
    /// The `Result` has to be `Ok`
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::UncheckedResultExt;
    ///
    /// let x: Result<u32, &str> = Ok(2);
    /// unsafe {
    ///     assert_eq!(x.unwrap_unchecked(), 2);
    /// }
    /// ```
    unsafe fn unwrap_unchecked(self) -> T;

    /// Unwraps a `Result`, yielding the content of an [`Err`][].
    ///
    /// # Safety
    ///
    /// The `Result` has to be `Err`.
    ///
    /// # Example
    ///
    /// ```
    /// use alloc_wg::UncheckedResultExt;
    ///
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// unsafe {
    ///     assert_eq!(x.unwrap_err_unchecked(), "emergency failure");
    /// }
    /// ```
    unsafe fn unwrap_err_unchecked(self) -> E;
}

unsafe fn unreachable() -> ! {
    debug_assert!(false);
    unreachable_unchecked()
}

impl<T> UncheckedOptionExt<T> for Option<T> {
    unsafe fn unwrap_unchecked(self) -> T {
        if let Some(t) = self { t } else { unreachable() }
    }

    unsafe fn unwrap_none_unchecked(self) {
        if self.is_some() {
            unreachable()
        }
    }
}

impl<T, E> UncheckedResultExt<T, E> for Result<T, E> {
    unsafe fn unwrap_unchecked(self) -> T {
        if let Ok(t) = self { t } else { unreachable() }
    }

    unsafe fn unwrap_err_unchecked(self) -> E {
        if let Err(t) = self { t } else { unreachable() }
    }
}
