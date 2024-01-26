//! Contains a trait extension for logging warnings before discarding them.
//!
//! This is built to work with [`log`] because it's the simplest, but due to [`tracing`]'s
//! interoperability, it will also work with it.
//!
//! This doesn't use macros mostly because the warning crate is better for method chaining and
//! macros make that awkward.
//!
//! [`tracing`]: https://docs.rs/tracing

use std::{error::Error, fmt::Debug, panic::Location};

use log::{log, Level};

use crate::Warning;

/// The private base function for all the logging stuff.
///
/// Note: since this is internal there's one finnicky bit:
/// make sure the first message has a space in it if you use it or it will look weird!
#[track_caller]
#[allow(clippy::obfuscated_if_else)]
fn log_and_continue<W, T>(
    warn: W,
    msg: Option<&'static str>,
    target: &str,
    level: Level,
    user_msg: Option<&str>,
) -> W
where
    W: Warning<T>,
    T: Debug,
    W::Err: Error,
{
    if warn.is_warning() {
        log!(
            target: target,
            level,
            "{}Call location: {}; Value being returned: {:?}; Warning being ignored: {}{}{}",
            msg.unwrap_or(""),
            Location::caller(),
            warn.inner_ref(),
            warn.err_ref().unwrap(),
            user_msg.is_some().then_some("; Custom Msg: ").unwrap_or(""),
            user_msg.unwrap_or(""),
        );
    }

    warn
}

/// A blanket impl'd trait extension that allows implementers of the [`Warning`] trait to do clean logging.
///
/// This is built to work with [`log`] because it's the simplest logging crate, but due to [`tracing`]'s
/// interoperability, it will also work with it.
///
/// This requires the underlying values be printable.
///
/// # Example:
/// ```
/// use warnable::{prelude::*, basic_warning::BasicWarning};
///
/// # use thiserror::Error;
/// # #[derive(Debug, Error)] #[error("placeholder")] struct CacheError;
///
/// fn very_long_computation() -> i32 // ...
/// # { 5 }
///
/// fn retrieve_from_cache(key: &str) -> Result<i32, CacheError> // ...
/// # { Err(CacheError) }
///
/// fn cache_or_compute(key: &str) -> BasicWarning<i32, CacheError> {
///     // Get it from the cache, or else do something we really don't want to do
///     // if we don't have to
///     retrieve_from_cache(key).recover(very_long_computation)
/// }
///
/// # fn main() {
/// let computed = cache_or_compute("my_key").warn_and_ignore("big_number_calculator");
/// let y = computed / 5;
/// // ...
/// # }
/// ```
///
/// [`tracing`]: https://docs.rs/tracing
pub trait WarningLogExt<T>: Warning<T>
where
    T: Debug,
    Self::Err: Error,
{
    /// If this has an associated error, will log said error without disturbing the inner structure.
    ///
    /// Useful for avoiding stuff like having to implement `map_err` and then do `.map_err(|e| { log!(e); e })`
    /// or whatever.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    fn log_and_continue_msg(self, target: &str, level: Level, msg: &str) -> Self {
        log_and_continue(self, None, target, level, Some(msg))
    }

    /// If this has an associated error, will log said error at the [`Level::Warn`] level,
    /// without disturbing the inner structure.
    ///
    /// Useful for avoiding stuff like having to implement `map_err` and then do `.map_err(|e| { log!(e); e })`
    /// or whatever.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    #[inline]
    fn warn_and_continue_msg(self, target: &str, msg: &str) -> Self {
        log_and_continue(self, None, target, Level::Warn, Some(msg))
    }

    /// If this has an associated error, will log said warning and discard it for the inner value.
    ///
    /// Essentially reduces to [`log_and_continue`](WarningLogExt::log_and_continue)
    /// followed by [`ignore`](Warning::ignore).
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    #[inline]
    fn log_and_ignore_msg(self, target: &str, level: Level, msg: &str) -> T {
        log_and_continue(self, Some("Ignored! "), target, level, Some(msg)).ignore()
    }

    /// If this has an associated error, will log said error at the [`Level::Warn`] level,
    /// and discard it for the inner value.
    ///
    /// Essentially reduces to [`warn_and_continue`](WarningLogExt::warn_and_continue)
    /// followed by [`ignore`](Warning::ignore).
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    #[inline]
    fn warn_and_ignore_msg(self, target: &str, msg: &str) -> T {
        log_and_continue(self, Some("Ignored! "), target, Level::Warn, Some(msg)).ignore()
    }

    /// If this has an associated error, will log said error without disturbing the inner structure.
    ///
    /// Useful for avoiding stuff like having to implement `map_err` and then do `.map_err(|e| { log!(e); e })`
    /// or whatever.
    #[track_caller]
    fn log_and_continue(self, target: &str, level: Level) -> Self {
        log_and_continue(self, None, target, level, None)
    }

    /// If this has an associated error, will log said error at the [`Level::Warn`] level,
    /// without disturbing the inner structure.
    ///
    /// Useful for avoiding stuff like having to implement `map_err` and then do `.map_err(|e| { log!(e); e })`
    /// or whatever.
    #[track_caller]
    #[inline]
    fn warn_and_continue(self, target: &str) -> Self {
        log_and_continue(self, None, target, Level::Warn, None)
    }

    /// If this has an associated error, will log said warning and discard it for the inner value.
    ///
    /// Essentially reduces to [`log_and_continue`](WarningLogExt::log_and_continue)
    /// followed by [`ignore`](Warning::ignore).
    #[track_caller]
    #[inline]
    fn log_and_ignore(self, target: &str, level: Level) -> T {
        log_and_continue(self, Some("Ignored! "), target, level, None).ignore()
    }

    /// If this has an associated error, will log said error at the [`Level::Warn`] level,
    /// and discard it for the inner value.
    ///
    /// Essentially reduces to [`warn_and_continue`](WarningLogExt::warn_and_continue)
    /// followed by [`ignore`](Warning::ignore).
    #[track_caller]
    #[inline]
    fn warn_and_ignore(self, target: &str) -> T {
        log_and_continue(self, Some("Ignored! "), target, Level::Warn, None).ignore()
    }
}

impl<T, W> WarningLogExt<T> for W
where
    W: Warning<T>,
    T: Debug,
    Self::Err: Error,
{
}

/// A trait for logging the error side of [`Result`] values without unwrapping them.
///
/// Useful for this kind of behavior:
/// ```
/// # use warnable::log::ResultLogErrorExt;
/// # use thiserror::Error;
/// # #[derive(Error, Debug)] #[error("placeholder")] struct ComputationError;
///
/// fn try_compute() -> Result<i32, ComputationError> {
///     // ...
/// #   Ok(15)
/// }
///
/// # fn main() -> Result<(),ComputationError> {
/// let x = try_compute().error_and_continue("my_subroutine")?;
/// let y = x * 2;
/// // ...
/// # Ok(())
/// # }
/// ```
///
/// Note that despite this being in the [`warnable`](crate) crate, this doesn't actually do anything
/// with the [`Warning`] trait. This is due to a lack of stable specialization. If we had it, we could
/// easily make this print errors *or* do the behavior of [`WarningLogExt`] in the case where the Result
/// holds a warning, but unfortunately that's not possible right now, and limiting the scope of the extension
/// just for usability with warnings feels like a waste.
///
/// For now, you'll have to settle for something like:
/// ```
/// # use warnable::{basic_warning::BasicWarning, log::{ResultLogErrorExt, WarningLogExt}};
/// # use thiserror::Error;
/// # #[derive(Error, Debug)] #[error("placeholder")] struct ComputationError;
/// # #[derive(Error, Debug)] #[error("placeholder")] struct FatalComputationError;
///
/// fn try_compute() -> Result<BasicWarning<i32,ComputationError>, FatalComputationError> {
///     // ...
/// #   Ok(15.into())
/// }
///
/// # fn main() -> Result<(),FatalComputationError> {
/// let x = try_compute().error_and_continue("my_subroutine")?.warn_and_ignore("my_subroutine");
/// let y = x * 2;
/// // ...
/// # Ok(())
/// # }
/// ```
pub trait ResultLogErrorExt {
    /// If this has an associated error, will log said error but otherwise keep the result.
    #[track_caller]
    fn log_and_continue(self, target: &str, level: Level) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Error`] level but otherwise keep the result.
    #[track_caller]
    fn error_and_continue(self, target: &str) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Warn`] level but otherwise keep the result.
    #[track_caller]
    fn warn_and_continue(self, target: &str) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Debug`] level but otherwise keep the result.
    #[track_caller]
    fn debug_and_continue(self, target: &str) -> Self;

    /// If this has an associated error, will log said error but otherwise keep the result.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    fn log_and_continue_msg(self, target: &str, level: Level, msg: &str) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Error`] level but otherwise keep the result.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    fn error_and_continue_msg(self, target: &str, msg: &str) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Warn`] level but otherwise keep the result.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    fn warn_and_continue_msg(self, target: &str, msg: &str) -> Self;

    /// If this has an associated error, will log said error at the [`Level::Debug`] level but otherwise keep the result.
    ///
    /// As with all `msg` variants, this allows passing a custom message.
    #[track_caller]
    fn debug_and_continue_msg(self, target: &str, msg: &str) -> Self;
}

/// Private common function to make the [`Result`] logging extension implementation neat and clean.
#[track_caller]
#[allow(clippy::obfuscated_if_else)]
fn result_log_and_continue<T, E>(
    result: Result<T, E>,
    target: &str,
    level: Level,
    msg: Option<&str>,
) -> Result<T, E>
where
    E: Error,
{
    result.map_err(|err| {
        log!(
            target: target,
            level,
            "Call location: {}; Error: {}{}{}",
            Location::caller(),
            err,
            msg.is_some().then_some("; Custom Msg: ").unwrap_or(""),
            msg.unwrap_or(""),
        );
        err
    })
}

impl<T, E> ResultLogErrorExt for Result<T, E>
where
    E: Error,
{
    fn log_and_continue_msg(self, target: &str, level: Level, msg: &str) -> Self {
        result_log_and_continue(self, target, level, Some(msg))
    }

    fn error_and_continue_msg(self, target: &str, msg: &str) -> Self {
        result_log_and_continue(self, target, Level::Error, Some(msg))
    }

    fn warn_and_continue_msg(self, target: &str, msg: &str) -> Self {
        result_log_and_continue(self, target, Level::Warn, Some(msg))
    }

    fn debug_and_continue_msg(self, target: &str, msg: &str) -> Self {
        result_log_and_continue(self, target, Level::Debug, Some(msg))
    }

    fn log_and_continue(self, target: &str, level: Level) -> Self {
        result_log_and_continue(self, target, level, None)
    }

    fn error_and_continue(self, target: &str) -> Self {
        result_log_and_continue(self, target, Level::Error, None)
    }

    fn warn_and_continue(self, target: &str) -> Self {
        result_log_and_continue(self, target, Level::Warn, None)
    }

    fn debug_and_continue(self, target: &str) -> Self {
        result_log_and_continue(self, target, Level::Debug, None)
    }
}
