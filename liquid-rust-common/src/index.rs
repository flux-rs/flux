/// Create an `usize` newtype that implements the [Index] trait.
#[macro_export]
macro_rules! new_index {
    ($(#[$attr:meta])* $index:ident) => {
        $(#[$attr])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $index(usize);

        impl $index {
            fn as_usize(&self) -> usize {
                self.0
            }
        }

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
