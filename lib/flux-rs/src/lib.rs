#![no_std]
#[cfg_attr(flux, flux::no_suggestions)]
pub mod bitvec;

pub use attrs::*;
pub use flux_attrs as attrs;

#[no_suggestions]
#[sig(fn(bool[true]) )]
pub fn assert(_: bool) {}

#[no_suggestions]
#[sig (fn() -> _ requires false)]
pub fn unreachable() -> ! {
    unreachable!("impossible case")
}

/// Macro for creating detached specifications.
///
/// # Example
/// ```
/// flux_rs::macros::detached_spec! {
///     fn inc(n:i32) -> i32[n+1];
///     fn watermelon(n:usize) -> usize[n+2];
/// }
/// ```
#[macro_export]
#[doc(hidden)]
macro_rules! __private_detached_spec {
    ($($e:tt)*) => {
        #[$crate::specs {
            $($e)*
        }]
        const _: () = ();
    };
}

/// Macro for creating `invariant qualifier`s
/// # Example
/// ```
/// invariant!(res: int, i: int, n: int ; res + i == n);
/// ```
#[macro_export]
#[doc(hidden)]
macro_rules! __private_invariant {
    ($($param:ident : $ty:ty),* ; $expr:expr) => {
        $crate::defs! {
            invariant qualifier Auto($($param: $ty),*) { $expr }
        }
        $crate::assert($expr);
    };
}

/// Macro for creating `invariant qualifier`s without an assertion.
///
/// Unlike [`invariant`](crate::macros::invariant), the body is never re-emitted as Rust, so it
/// may use refinement-only syntax. Sorts are inferred; annotate the ones that can't be, using
/// the same `params ; body` syntax as [`invariant`](crate::macros::invariant).
///
/// # Example
/// ```
/// flux_rs::macros::qualifier!(my_plus(res, i) == n);
/// flux_rs::macros::qualifier!(res: int, i: int ; res + i == n);
/// ```
#[macro_export]
#[doc(hidden)]
macro_rules! __private_qualifier {
    ($($param:ident : $ty:ty),+ ; $($body:tt)*) => {
        $crate::defs! {
            invariant qualifier Auto($($param: $ty),+) { $($body)* }
        }
    };
    ($($body:tt)*) => {
        $crate::defs! {
            invariant qualifier Auto() { $($body)* }
        }
    };
}

pub mod macros {
    /// Macro for creating detached specifications.
    ///
    /// # Example
    /// ```
    /// flux_rs::macros::detached_spec! {
    ///     fn inc(n:i32) -> i32[n+1];
    ///     fn watermelon(n:usize) -> usize[n+2];
    /// }
    /// ```
    pub use crate::__private_detached_spec as detached_spec;
    /// Macro for creating `invariant qualifier`s
    /// # Example
    /// ```
    /// flux_rs::macros::invariant!(res: int, i: int, n: int ; res + i == n);
    /// ```
    pub use crate::__private_invariant as invariant;
    /// Macro for creating a local `invariant qualifier` hint.
    /// # Example
    /// ```
    /// flux_rs::macros::qualifier!(my_plus(res, i) == n);
    /// flux_rs::macros::qualifier!(res: int, i: int ; res + i == n);
    /// ```
    pub use crate::__private_qualifier as qualifier;
}
