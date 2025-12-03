#![no_std]
pub mod bitvec;

pub use attrs::*;
pub use flux_attrs as attrs;

#[sig(fn(bool[true]) )]
pub fn assert(_: bool) {}

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
        #[flux_rs::specs {
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
        #[flux::defs{
            invariant qualifier Auto($($param: $ty),*) { $expr }
        }]
        const _: () = ();
        flux_rs::assert($expr);
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
}
