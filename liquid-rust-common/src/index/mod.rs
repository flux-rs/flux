//! Utilities to index stuff in a type safe way using newtypes.
mod generator;
mod map;

pub use generator::IndexGen;
pub use map::IndexMap;

/// Create an `usize` newtype that implements the [Index] trait.
#[macro_export]
macro_rules! new_index {
    ($(#[$attr:meta])* $index:ident) => {
        $(#[$attr])*
        pub struct $index(usize);

        impl $crate::index::Index for $index {
            fn new(index: usize) -> Self {
                Self(index)
            }

            fn index(self) -> usize {
                self.0
            }
        }
    };
}

/// Utility trait to define new indices.
///
/// This trait should not be implemented by hand. Use the [new_index] macro instead.
pub trait Index: Sized {
    fn new(index: usize) -> Self;
    fn index(self) -> usize;
}

