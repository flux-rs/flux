use std::{any, collections::HashMap};

/// Create an `usize` newtype that implements the [Index] trait.
#[macro_export]
macro_rules! new_index {
    ($(#[$attr:meta])* $index:ident) => {
        $(#[$attr])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// A generator of fresh indices.
///
/// It can generate any index created with the [new_index] macro.
///
/// If you use more than one [IndexGen] uniqueness is only guaranteed for indices that come from
/// the same generator.
#[derive(Default)]
pub struct IndexGen {
    map: HashMap<any::TypeId, usize>,
}

impl IndexGen {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Generate a fresh index of type `T`.
    ///
    /// ```
    /// # use liquid_rust_common::index::IndexGen;
    /// # use liquid_rust_common::new_index;
    /// new_index!(Idx);
    /// let mut gen = IndexGen::new();
    /// let idx1: Idx = gen.fresh();
    /// let idx2: Idx = gen.fresh();
    /// assert_ne!(idx1, idx2);
    /// ```
    pub fn fresh<T: any::Any + Index>(&mut self) -> T {
        let next = self.map.entry(any::TypeId::of::<T>()).or_default();
        *next += 1;
        T::new(*next - 1)
    }
}
