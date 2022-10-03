use std::convert::Infallible;

/// Unwraps a `Result<T, Infallible>`.
pub(crate) fn unwrap_infallible<T>(res: Result<T, Infallible>) -> T {
    match res {
        Ok(val) => val,
        Err(err) => match err {},
    }
}
