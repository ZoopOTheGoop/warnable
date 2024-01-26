//! Contains basic convenience implementations of the core traits

use crate::Warning;

/// A rudimentary [`Warning`], that simply takes in any type and error.
/// This should be fine for most cases, albeit unglamorous.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(serde, derive(Serialize, Deserialize))]
pub enum BasicWarning<T, E> {
    Ok(T),
    Warn(T, E),
}

impl<T, E> BasicWarning<T, E> {
    /// Applies the passed in closure, mapping the inner value to the result of said
    /// closure, regardless of warning status. This works effectively like any other `map`
    /// function in Rust.
    ///
    /// ## Example
    /// ```
    /// use warnable::{prelude::*, basic_warning::BasicWarning};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct TestWarning;
    ///
    /// let warn = BasicWarning::from(15);
    ///
    /// let warn = warn.map(|v| v as f64 * 10.0);
    ///
    /// assert_eq!(warn, BasicWarning::Ok(150.0));
    ///
    /// let warn = warn.to_warning(TestWarning);
    ///
    /// let warn = warn.map(|v| v as i64 + 1);
    ///
    /// assert_eq!(warn, BasicWarning::Warn(151, TestWarning))
    /// ```
    pub fn map<F, U>(self, f: F) -> BasicWarning<U, E>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::Ok(val) => BasicWarning::Ok(f(val)),
            Self::Warn(val, err) => BasicWarning::Warn(f(val), err),
        }
    }

    /// Applies the passed in closure, mapping the inner error to the result of said
    /// closure, regardless of warning status. This will always change the type, but
    /// will only execute the closure when this is a warning and not [`Ok`](BasicWarning::Ok).
    ///
    /// It's essentially [`Result::map_err`] but for a [`Warning`].
    ///
    /// ## Example
    /// ```
    /// use warnable::{prelude::*, basic_warning::BasicWarning};
    ///
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct TestWarning;
    /// # #[derive(Debug, PartialEq, Eq)]
    /// struct TestWarning2;
    ///
    /// let warn = BasicWarning::<_, TestWarning>::from(15);
    ///
    /// let warn = warn.map_err(|e| TestWarning2);
    /// assert_eq!(warn, BasicWarning::Ok(15));
    ///
    /// let warn = warn.to_warning(TestWarning2);
    /// assert_eq!(warn, BasicWarning::Warn(15, TestWarning2));
    ///
    /// let warn = warn.map_err(|e| TestWarning);
    /// assert_eq!(warn, BasicWarning::Warn(15, TestWarning))
    /// ```
    pub fn map_err<F, U>(self, f: F) -> BasicWarning<T, U>
    where
        F: FnOnce(E) -> U,
    {
        match self {
            Self::Ok(val) => BasicWarning::Ok(val),
            Self::Warn(val, err) => BasicWarning::Warn(val, f(err)),
        }
    }
}

impl<T, E> Warning<T> for BasicWarning<T, E> {
    type Err = E;

    fn is_ok(&self) -> bool {
        matches!(self, BasicWarning::Ok(_))
    }

    fn err(self) -> Option<Self::Err> {
        if let Self::Warn(_, err) = self {
            Some(err)
        } else {
            None
        }
    }

    fn to_warning(self, err: Self::Err) -> Self {
        match self {
            Self::Warn(_, _) => {
                panic!("Cannot convert into warning, we're already a warning!");
            }
            Self::Ok(v) => BasicWarning::Warn(v, err),
        }
    }

    fn from_err(val: T, err: Self::Err) -> Self {
        Self::Warn(val, err)
    }

    fn ignore(self) -> T {
        match self {
            Self::Ok(val) | Self::Warn(val, _) => val,
        }
    }

    fn inner_ref(&self) -> &T {
        match self {
            Self::Ok(val) | Self::Warn(val, _) => val,
        }
    }

    fn err_ref(&self) -> Option<&Self::Err> {
        match self {
            Self::Warn(_, err) => Some(err),
            Self::Ok(_) => None,
        }
    }
}

impl<T, E> From<T> for BasicWarning<T, E> {
    fn from(value: T) -> Self {
        Self::Ok(value)
    }
}
