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
/// detached_spec! {
///     fn inc(n:i32) -> i32[n+1];
///     fn watermelon(n:usize) -> usize[n+2];
/// }
/// ```
#[macro_export]
macro_rules! detached_spec {
    ($($e:tt)*) => {
        #[flux_rs::specs {
            $($e)*
        }]
        const _: () = ();
    };
}
