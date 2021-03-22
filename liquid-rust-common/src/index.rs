pub use rustc_index::{
    newtype_index,
    vec::{Idx, IndexVec},
};

use std::{marker::PhantomData, sync::atomic::AtomicUsize};

/// A generator of fresh indices.
///
/// It can generate any index created with the [newtype_index] macro.
///
/// If you use more than one [IndexGen] uniqueness is only guaranteed for indices that come from
/// the same generator.
pub struct IndexGen<I> {
    count: AtomicUsize,
    _marker: PhantomData<I>,
}

impl<I: Idx> IndexGen<I> {
    pub fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
            _marker: PhantomData,
        }
    }

    /// Generate a fresh index of type `I`.
    ///
    /// ```
    /// # use liquid_rust_common::index::IndexGen;
    /// # use liquid_rust_common::new_index;
    /// newtype_index!(Idx);
    /// let mut gen = IndexGen::new();
    /// let idx1: Idx = gen.fresh();
    /// let idx2: Idx = gen.fresh();
    /// assert_ne!(idx1, idx2);
    /// ```
    pub fn fresh(&self) -> I {
        let index = self
            .count
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        I::new(index)
    }
}
