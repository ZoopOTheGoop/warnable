//! This crate exists for one key purpose: propogating and cleanly handling non-fatal error information.
//! If you just want to get started jump to [usage](#usage), otherwise let's get started with the:
//!
//! ## Motivation
//!
//! In general, Rust allows for recovery from non-fatal [`Error`]s simply by using the [`Result`] type -
//! either something succeeded and returned a value, or it failed and there was some error. You can then
//! choose to handle the error, recover, and discard it, or "bubble it up" whether that be by
//! [`panic!`] or [`?`](std::ops::Try).
//!
//! This usually works well, and leads to the general Rust error handling strategy: bubble up the error
//! and let the consumer decide what to do with it. This gives a lot of flexibility especially in library code,
//! and reduces coupling for things like error handling packages.
//!
//! But what about the case where errors are recoverable, but notable? Bubbling them up to the caller is often
//! somewhat ugly:
//!
//! ```no_run
//! # struct NonFatalError;
//! # struct FatalError;
//! #
//! fn my_computation() -> (f64, Option<NonFatalError>) // ...
//! # {
//! # (1.5, None)
//! # }
//!
//! #[must_use]
//! fn failable(val: f64) -> Result<f64, FatalError> // ...
//! # {
//! # Ok(5.0 * val)
//! # }
//!
//! fn calls_my_computation() -> Result<(f64, Option<NonFatalError>), FatalError> {
//!     let (val, maybe_err) = my_computation();
//!     
//!     Ok((failable(val)?, maybe_err))
//! }
//! ```
//!
//! This on its own isn't *too* bad, but it does mean that we essentially have to pollute almost every call
//! signature until the top level with a tuple, destructure it at every call site, and then zip it back up
//! for the return. And that's assuming we don't want to *do* anything with the warning value at all.
//!
//! The following is the motivating example that inspired this crate: bubbling up the info that a cache connection is borked,
//! while *hopefully* getting it from the database in the case that happens.
//!
//! ```no_run
//! struct CacheError;
//!
//! struct DBError;
//!
//! struct StorageError {
//!     dbe: DBError,
//!     ce: CacheError
//! }
//!
//! fn check_cache<T>(key: &str) -> Result<T, CacheError> // ...
//! # {
//! # Err(CacheError)
//! # }
//!
//! fn check_db<T>(key: &str) -> Result<T, DBError> // ...
//! # {
//! # Err(DBError)
//! # }
//!
//! fn get_from_storage<T>(key: &str) -> Result<(T, Option<CacheError>), StorageError> {
//!    // ???
//! # Err(StorageError { dbe: DBError, ce: CacheError} )
//! }
//! ```
//!
//! There are many ways to fill in the mystery section, but none of them are pretty
//!
//! ```no_run
//! # struct CacheError;
//! # struct DBError;
//! # struct StorageError { dbe: DBError, ce: CacheError }
//! # fn check_cache<T>(key: &str) -> Result<T, CacheError> { Err(CacheError) }
//! # fn check_db<T>(key: &str) -> Result<T, DBError> { Err(DBError) }
//! fn get_from_storage<T>(key: &str) -> Result<(T, Option<CacheError>), StorageError> {
//!     match check_cache(key) {
//!         Ok(val) => Ok((val, None)),
//!         Err(cache_err) => match check_db(key) {
//!             Ok(val) => Ok((val, Some(cache_err))),
//!             Err(db_err) => Err(StorageError { ce: cache_err, dbe: db_err })
//!         }
//!     }
//! }
//! ```
//!
//! Or maybe
//!
//! ```no_run
//! # #[derive(Copy,Clone)] struct CacheError;
//! # #[derive(Copy,Clone)] struct DBError;
//! # struct StorageError { dbe: DBError, ce: CacheError }
//! # fn check_cache<T>(key: &str) -> Result<T, CacheError> { Err(CacheError) }
//! # fn check_db<T>(key: &str) -> Result<T, DBError> { Err(DBError) }
//! fn get_from_storage<T>(key: &str) -> Result<(T, Option<CacheError>), StorageError> {
//!     check_cache(key)
//!     .map(|val| (val, None))
//!     .or_else(|e|
//!         check_db(key)
//!         .map(|val| (val, Some(e)))
//!         .map_err(|e2| StorageError { ce: e, dbe: e2 })
//!     )
//! }
//! ```
//!
//! (And even that doesn't work if your types aren't [`Copy`], or [`Clone`] with some added calls).
//!
//! There are many ways of doing this, some of them almost certainly better than what I've listed here.
//! Things like [`thiserror`](https://docs.rs/thiserror/) and [`anyhow`](https://docs.rs/anyhow/)
//! can definitely help to one degree or another. But overall this is generally not fun to deal with.
//! In most cases, the solution is probably just to log (more on that [later](#logging)) and move on:
//!
//! ```no_run
//! # use log::warn;
//! # use thiserror::Error;
//! # #[derive(Copy, Clone, Debug, Error)] #[error("cache problem")] struct CacheError;
//! # #[derive(Copy,Clone)] struct DBError;
//! # struct StorageError { dbe: DBError, ce: CacheError }
//! # fn check_cache<T>(key: &str) -> Result<T, CacheError> { Err(CacheError) }
//! # fn check_db<T>(key: &str) -> Result<T, DBError> { Err(DBError) }
//! fn get_from_storage<T>(key: &str) -> Result<T, DBError> {
//!     let cache_result = check_cache(key);
//!     match cache_result {
//!         Ok(val) => { return Ok(val); },
//!         Err(err) => warn!("cache problem: {}; trying database for {}", err, key),
//!     }
//!     
//!     check_db(key)
//! }
//! ```
//!
//! Not too bad, but in my opinion it's also not necessarily ideal. The two logging frameworks for Rust
//! are genuinely very good at configurability, so you can absolutely log from within a library or whatever else without
//! your consumer having to deal with all the messages, and on top of that [`tracing`](https://docs.rs/tracing/)
//! is even compatible with [`log`](https://docs.rs/log/)! (Albeit not vice versa)
//!
//! But sometimes it can genuinely feel better to just let the information propogate up to the top until
//! the application code or some sort of sentinel or other handler can see, acknowledge, and do the appropriate
//! thing. Maybe you need to wait until you're out of generic code to handle the warning.
//! This is sometimes best whether the correct action be logging, sending an email,
//! marking that the cache is dirty and can't be trusted, or whatever else.
//!
//! ## Usage
//!
//! This crate's primary feature is the [`Warning`] trait alongside various trait extensions you probably won't
//! have to *directly* deal with much, but give you a lot of tools.
//!
//! Let's revisit our cache and database example from earlier. First of all, as of now this crate does
//! involve making a few extra types and some boilerplate (this may be able to be alleviated with derive macros
//! later on). But let's start by getting set up:
//!
//! ```
//! use warnable::prelude::*;
//!
//! # #[derive(PartialEq, Eq, Debug)]
//! struct CacheError;
//! # #[derive(PartialEq, Eq, Debug)]
//! struct DBError;
//!
//! # #[derive(PartialEq, Eq, Debug)]
//! struct StorageError
//! {
//!     dbe: DBError,
//!     ce: CacheError
//! }
//!
//! impl Combineable<DBError> for CacheError {
//!     type Combined = StorageError;
//!
//!     fn combine(self, other: DBError) -> StorageError {
//!         StorageError { ce: self, dbe: other }
//!     }
//! }
//!
//! # assert_eq!(CacheError.combine(DBError), StorageError { ce: CacheError, dbe: DBError })
//! ```
//!
//! This lets us combine two errors (not necessarily, but usually, actual [`Error`]s) into a larger one.
//! This covers our case where two (or more) consecutive failures compound to be an actual error. In practice,
//! you could probably defer to something like [`anyhow::Context`](https://docs.rs/anyhow/latest/anyhow/trait.Context.html)
//! if you wanted to and were okay with erasing the type to some degree.
//!
//! Next, let's create our warning. If you want something simple, feel free to go with [`BasicWarning`],
//! but for the sake of example let's build our own real quick.
//!
//! ```
//! # use warnable::prelude::*;
//!
//! # #[derive(PartialEq, Eq, Debug)]
//! # pub struct CacheError;
//! # #[derive(PartialEq, Eq, Debug)]
//! # struct DBError;
//! # #[derive(PartialEq, Eq, Debug)]
//! # struct StorageError { dbe: DBError, ce: CacheError }
//!
//! pub struct CacheWarning<T>(T, Option<CacheError>);
//!
//! impl<T> Warning<T> for CacheWarning<T> {
//!     type Err = CacheError;
//!
//!     fn is_ok(&self) -> bool {
//!         self.1.is_none()
//!     }
//!
//!     fn inner_ref(&self) -> &T {
//!         &self.0
//!     }
//!
//!     fn ignore(self) -> T {
//!         self.0
//!     }
//!
//!     fn err(self) -> Option<Self::Err> {
//!         self.1
//!     }
//!
//!     fn err_ref(&self) -> Option<&Self::Err> {
//!         self.1.as_ref()
//!     }
//!
//!     fn to_warning(mut self, err: Self::Err) -> Self {
//!         assert!(self.1.is_none(), "This is already a warning!");
//!         self.1 = Some(err);
//!         self
//!     }
//!
//!     fn from_err(val: T, err: Self::Err) -> Self {
//!         CacheWarning(val, Some(err))
//!     }
//! }
//!
//! // And finally...
//!
//! impl<T> From<T> for CacheWarning<T> {
//!     fn from(val: T) -> Self {
//!         CacheWarning(val, None)
//!     }
//! }
//! ```
//!
//! Definitely some boilerplate, most of it probably custom derivable away, but with this, everything else we
//! need gets auto-implemented!
//!
//! Let's revisit our example from earlier now:
//!
//! ```
//! use warnable::prelude::*;
//! # use thiserror::Error;
//! # #[derive(PartialEq, Eq, Debug, Error)] #[error("cache issue")]
//!  pub struct CacheError;
//! # #[derive(PartialEq, Eq, Debug)]
//!  struct DBError;
//! # #[derive(PartialEq, Eq, Debug)]
//!  struct StorageError { dbe: DBError, ce: CacheError }
//!
//! impl Combineable<DBError> for CacheError // ...
//! # {
//! # type Combined = StorageError;
//! # fn combine(self, other: DBError) -> StorageError { StorageError { dbe: other, ce: self } }
//! # }
//!
//! pub struct CacheWarning<T>(T, Option<CacheError>);
//!
//! impl<T> Warning<T> for CacheWarning<T> {
//!     // ...
//! #    type Err = CacheError;
//! #
//! #    fn is_ok(&self) -> bool {
//! #        self.1.is_none()
//! #    }
//! #
//! #    fn inner_ref(&self) -> &T {
//! #        &self.0
//! #    }
//! #
//! #    fn ignore(self) -> T {
//! #        self.0
//! #    }
//! #
//! #    fn err(self) -> Option<Self::Err> {
//! #        self.1
//! #    }
//! #
//! #    fn err_ref(&self) -> Option<&Self::Err> {
//! #        self.1.as_ref()
//! #    }
//! #
//! #    fn to_warning(mut self, err: Self::Err) -> Self {
//! #        assert!(self.1.is_none(), "This is already a warning!");
//! #        self.1 = Some(err);
//! #        self
//! #   }
//! #
//! #    fn from_err(val: T, err: Self::Err) -> Self {
//! #        CacheWarning(val, Some(err))
//! #    }
//! # }
//! #
//! # impl<T> From<T> for CacheWarning<T> {
//! #    fn from(val: T) -> Self {
//! #        CacheWarning(val, None)
//! #    }
//! }
//!
//! fn check_cache(key: &str) -> Result<i64, CacheError> // ...
//! # {
//! #    Err(CacheError)
//! # }
//!
//! fn check_db(key: &str) -> Result<i64, DBError> // ...
//! # {
//! #   Ok(5)
//! # }
//!
//! fn get_from_storage(key: &str) -> Result<CacheWarning<i64>, StorageError> {
//!     check_cache(key).try_recover(|| check_db(key))
//! }
//!
//! # fn main() -> Result<(), StorageError> {
//! let seed = get_from_storage("big_value")?;
//! if seed.is_warning() {
//!     eprintln!("There was a cache problem: {}", seed.err_ref().unwrap());
//! }
//!
//! let more_computation = seed.ignore() / 5;
//! // ...
//! # assert_eq!(more_computation, 1);
//! # Ok(())
//! # }
//! ```
//!
//! This is much easier to read. Of course, this is taking advantage of [`ignore`](Warning::ignore),
//! it's not doing much with the result itself. We can do that, but sadly one limitation at present is that
//! since GATs aren't really able to do something like `Mappable`/`Functor`, we can't cleanly make
//! [`Warning`] types implement something like `map`. That said, [`BasicWarning`] does have this ([`BasicWarning::map`]
//! and [`BasicWarning::map_err`]), so please use that or you'll have to implement it yourself, sadly.
//!
//! ### Surefire recovery
//!
//! In addition to compounding errors, there's another function added to any [`Result`] containing a
//! type that can become a [`Warning`]: [`ResultRecoverExt::recover`].
//!
//! This allows us to recover from something fallible with a *surefire* (but non-ideal) method of getting the answer,
//! while still retaining the error information:
//!
//! ```
//! # use warnable::prelude::*;
//! # #[derive(PartialEq, Eq, Debug)]
//! struct CacheError;
//!
//! // Let's use BasicWarning for now
//! type CacheWarning<T> = BasicWarning<T, CacheError>;
//!
//! fn check_cache(key: &str) -> Result<i64, CacheError> // ...
//! # {
//! #    Err(CacheError)
//! # }
//!
//! fn super_expensive_function() -> i64 // It's extremely expensive I'm warning you
//! # {
//! # "Nvidia A100 GPU lined with emeralds and a copy of .hack//Quarantine for the PS2".chars().count() as i64
//! # }
//!
//! fn cache_or_compute(key: &str) -> CacheWarning<i64> {
//!     check_cache(key).recover(|| super_expensive_function())
//! }
//!
//! # fn main() {
//!     let computation = cache_or_compute("please_be_there").map(|v| v * 100);
//!     // ...
//! # assert_eq!(BasicWarning::Warn(7900, CacheError), computation)
//! # }
//! ```
//!
//! [`Error`]: std::error::Error
#![cfg_attr(
    feature = "log",
    doc = r#"
## Logging
 
In addition to the primary features, this crate also provides some extensions when the `log` feature is enabled.
This allows for some nice method chaining for common cases even when "log and move on" is 
what you want to do at a certain point.

Due to the focus on method chaining, this is not a *fully featured* log suite. If you need to use all the log features
at your disposal, you'll still need to manually wire it up, there was no point in reinventing the wheel with macros
and proc macros when those are already in a good state.

However, it does allow some little conveniences:

```
# use warnable::prelude::*;
# use thiserror::Error;
#
# #[derive(PartialEq, Eq, Error, Debug)]
# #[error("problem with cache")]
# struct CacheError;
# #[derive(Debug)]
# struct DBError;
# #[derive(Debug)]
# struct StorageError { dbe: DBError, ce: CacheError }
# 
# impl Combineable<DBError> for CacheError {
# type Combined = StorageError;
# fn combine(self, other: DBError) -> StorageError { StorageError { dbe: other, ce: self }}
# }
# 
# // Let's use BasicWarning for now
# type CacheWarning<T> = BasicWarning<T, CacheError>;

fn check_cache(key: &str) -> Result<i64, CacheError> // ...
# {
#    Err(CacheError)
# }

fn check_db(key: &str) -> Result<i64, DBError> // ...
# {
#   Ok(5)
# }

fn get_from_storage(key: &str) -> Result<i64, StorageError> {
    // We need to do this for type inference
    let warning: CacheWarning<_> = check_cache(key).try_recover(|| check_db(key))?;
    Ok(warning.warn_and_ignore("storage utils"))
}

# fn main() -> Result<(), StorageError> {
let computation = get_from_storage("please_be_there")? * 100;
# assert_eq!(computation, 500);
# Ok(())
# }
```

Even when you're not using [`Warning`] functionality, you can do some basic in-place logging
of [`Result`]. Here's an example using the [`thiserror`](https://docs.rs/thiserror/latest/thiserror/)
crate:

```
use warnable::prelude::*;
use thiserror::Error;

#[derive(Error, Debug)] 
#[error("Could not run foo")] 
struct FooFailure;

fn foo() -> Result<i64, FooFailure> 
# {
#   Err(FooFailure) 
# }

let value = foo().warn_and_continue("foo_caller").unwrap_or(5);
```

This will log an error if `foo` returns one, before defaulting to `5`.

For more examples please see further examples on the trait extensions themselves
in the [`log`](warnable::log) module. Please understand that to use this functionality
you do have to ensure that `T` is [`Debug`] and the error type is [`Error`] so that
their values can actually be written.

All of these functions use [`#\[track_caller\]`] so that they can accurately log the file, line, and column
of the calling function in their attached error message.

[`#\[track_caller\]`]: https://rustc-dev-guide.rust-lang.org/backend/implicit-caller-location.html
"#
)]

pub mod basic_warning;
#[cfg(any(feature = "log", feature = "tracing"))]
pub mod log;

/// The crate prelude, meaning that for maximum use you probably just want to do
///
/// ```
/// use warnable::prelude::*;
/// ```
///
/// At the top of your module.
pub mod prelude {
    #[cfg(any(feature = "log", feature = "tracing"))]
    pub use crate::log::{ResultLogErrorExt, WarningLogExt};
    pub use crate::{
        basic_warning::BasicWarning, Combineable, Recoverable, ResultRecoverExt,
        ResultTryRecoverExt, Warning,
    };
}

pub use basic_warning::BasicWarning;

/// The [`Warning`] trait allows a type to designate that it should potentially
/// be treated as a warning. This is similar to a [`Result`] in concept, except that
/// instead of an error, its second side contains both a value *and* an error, which denotes
/// some sort of recovered issue with computation.
///
/// This is done as a trait because unlike [`BasicWarning`] it's possible to contain
/// your value within the error itself.
///
/// All [`Warning`]s must implement [`From`] for their underlying type(s), which should construct
/// them in the "ok" state (i.e. no warning has occurred).
pub trait Warning<T>: Sized + From<T> {
    /// The underlying error. This generally will, but does not have to, implement [`Error`](std::error::Error).
    type Err;

    /// Returns `true` if the underlying value is a successful computation.
    fn is_ok(&self) -> bool;

    /// Returns `true` if the underlying value denotes an error was recovered from.
    fn is_warning(&self) -> bool {
        !self.is_ok()
    }

    /// Returns a reference to the inner value.
    fn inner_ref(&self) -> &T;

    /// Deconstructs the type and returns the underlying value, this will always succeed because
    /// both branches much have an associated value.
    ///
    /// This essentially "ignores" the warning (if any), hence the name.
    ///
    /// If you want to force checking for a warning first, use [`Warning::to_result`]
    fn ignore(self) -> T;

    /// Deconstructs the type and returns the underlying error. This will return [`None`] in the case
    /// where [`is_ok`](Warning::is_ok) is `true` (i.e. nothing is amiss, no error has occurred).
    fn err(self) -> Option<Self::Err>;

    /// Returns a reference to the inner error.
    fn err_ref(&self) -> Option<&Self::Err>;

    /// Converts this value into a warning instead of just a value. This should [`panic!`] if the type
    /// was already a warning.
    fn to_warning(self, err: Self::Err) -> Self;

    /// Constructs a new warning of this type from a value and an error, indicating that while a
    /// solution was eventually reached, an error worth warning about was received in the process.
    fn from_err(val: T, err: Self::Err) -> Self;

    /// Deconstructs the type and treats it as if it were a [`Result`] where [`Err`] denotes
    /// an error and not simply a warning attached to a successful computation. If this is currently
    /// a warning, the underlying value will be discarded. If there is no attached warning, this
    /// is equivalent to [`Warning::ignore`].
    fn to_result(self) -> Result<T, Self::Err> {
        if self.is_ok() {
            Ok(self.ignore())
        } else {
            Err(self.err().unwrap())
        }
    }
}

/// A [`Combineable`] is a type (usually an error) that can combine with another type (also usually an error)
/// in order to create a type containing info about both. Kind of like [`Add`], but for errors.
///
/// This is *not* symmetric (i.e. `impl Combineable<E1> for E2` does not imply `impl Combineable<E2> for E1`),
/// this is because two errors happening in different orders may have different semantics.
///
/// This trait's methods are rarely used directly, and typically is only called from part of [`Recoverable`].
///
/// [`Add`]: std::ops::Add
pub trait Combineable<E> {
    /// The error these two will combine into.
    type Combined;

    /// Combines the two errors into their unified type.
    fn combine(self, other: E) -> Self::Combined;
}

/// An error (usually an implementor of [`Error`]) is [`Recoverable`] when there's another computation that,
/// if successful, means that our error was not fatal.
///
/// If said computation succeeds, this error will be converted into a [`Warning`] in its warning state along
/// with the successfully computed value, otherwise this will be [`combine`]d with the error from the other
/// failed computation.
///
/// You may use this directly, but may find the [`ResultTryRecoverExt::try_recover`] option more ergonomic in most cases.
///
/// [`combine`]: Combineable::combine
/// [`Error`]: std::error::Error
pub trait Recoverable<E>: Combineable<E> + Sized {
    /// The [`Warning`] this error will be converted into if successfully recovered from.
    type Warning<T>: Warning<T, Err = Self>;

    /// Recover from this error with the given value. Useful if computation
    /// can't or is best not put in a closure.
    ///
    /// This is ultimately just [`Warning::from_err`].
    fn recover<T>(self, val: T) -> Self::Warning<T> {
        Self::Warning::from_err(val, self)
    }

    /// Attempt to recover from this error, if the closure returns [`Ok`], then this error
    /// will be converted into the associated [`Recoverable::Warning`], otherwise it will
    /// return an [`Err`] [`combine`]ing the two errors.
    ///
    /// [`combine`]: Combineable::combine
    fn try_recover<T, F>(self, closure: F) -> Result<Self::Warning<T>, Self::Combined>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match closure() {
            Ok(val) => Ok(self.recover(val)),
            Err(err) => Err(self.combine(err)),
        }
    }
}

pub trait ResultRecoverExt<T, W, E>: Sized
where
    W: Warning<T, Err = E>,
{
    // "as" works here because we're doing a free trait -> real conversion
    #[doc(hidden)]
    #[allow(clippy::wrong_self_convention)]
    fn as_result(self) -> Result<T, E>;

    /// Converts this result into a warning after recovering with a surefire computation.
    fn recover<F>(self, f: F) -> W
    where
        F: FnOnce() -> T,
    {
        match self.as_result() {
            Ok(val) => val.into(),
            Err(err) => W::from_err(f(), err),
        }
    }
}

/// An extension trait for [`Result`] that allows attempts to recover from failable computations.
///
/// ```
/// # use warnable::{prelude::*, basic_warning::BasicWarning};
/// # #[derive(Debug)] struct CacheError;
/// # #[derive(Debug)] struct DatabaseError;
/// # #[derive(Debug)] struct RetrievalError(CacheError,DatabaseError);
/// #
/// # impl Combineable<DatabaseError> for CacheError {
/// #   type Combined = RetrievalError;
/// #
/// #   fn combine(self, other: DatabaseError) -> RetrievalError { RetrievalError(self, other) }
/// # }
/// #
/// # impl Recoverable<DatabaseError> for CacheError {
/// #   type Warning<T> = BasicWarning<T, Self>;
/// # }
/// #
/// # type CacheWarning<T> = BasicWarning<T, CacheError>;
/// #
/// # struct MyCache;
/// # impl MyCache {
/// #   fn get_num(&self, key: &str) -> Result<i32, CacheError> { Err(CacheError) }
/// # }
/// #
/// # struct MyDB;
/// # impl MyDB {
/// #   fn query_num(&self, key: &str) -> Result<i32, DatabaseError> { Err(DatabaseError) }
/// # }
///
/// // Suppose both the Cache and DB have their own errors.
/// # fn cache_or_fallback(cache: MyCache, db: MyDB) -> Result<CacheWarning<i32>, RetrievalError> {
/// cache.get_num("oops, cache is down").try_recover(|| db.query_num("oops DB is down"))
/// // ...
/// #
/// # }
/// #
/// # cache_or_fallback(MyCache, MyDB);
/// ```
pub trait ResultTryRecoverExt<T, W, E, E2>: Sized + ResultRecoverExt<T, W, E>
where
    W: Warning<T, Err = E>,
    E: Combineable<E2>,
{
    /// Attempts to recover from another fallable computation, if it succeeds, the
    /// error becomes a warning, otherwise the errors become unified.
    #[track_caller]
    fn try_recover<F>(self, f: F) -> Result<W, E::Combined>
    where
        F: FnOnce() -> Result<T, E2>,
    {
        match self.as_result() {
            Ok(val) => Ok(val.into()),
            Err(err) => match f() {
                Ok(val) => Ok(W::from_err(val, err)),
                Err(e2) => Err(err.combine(e2)),
            },
        }
    }
}

impl<T, W, E> ResultRecoverExt<T, W, E> for Result<T, E>
where
    W: Warning<T, Err = E>,
{
    #[inline(always)]
    #[doc(hidden)]
    fn as_result(self) -> Self {
        self
    }
}

impl<T, W, E, E2> ResultTryRecoverExt<T, W, E, E2> for Result<T, E>
where
    W: Warning<T, Err = E>,
    E: Combineable<E2>,
{
}
