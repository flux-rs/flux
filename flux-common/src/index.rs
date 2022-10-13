use std::{marker::PhantomData, sync::atomic::AtomicUsize};

pub use rustc_index::vec::{Idx, IndexVec};

/// A generator of fresh indices.
///
/// It can generate any index created with the [`newtype_index`] macro.
///
/// If you use more than one [IndexGen] uniqueness is only guaranteed for indices that come from
/// the same generator.
///
/// [`newtype_index`]: rustc_index::newtype_index
pub struct IndexGen<I> {
    count: AtomicUsize,
    _marker: PhantomData<I>,
}

impl<I: Idx> IndexGen<I> {
    pub fn new() -> Self {
        Self { count: AtomicUsize::new(0), _marker: PhantomData }
    }

    pub fn skipping(skip: usize) -> Self {
        let gen = IndexGen::new();
        gen.skip(skip);
        gen
    }

    /// Generate a fresh index of type `I`.
    ///
    /// ```ignore
    /// # use flux_common::index::IndexGen;
    /// # use flux_common::newtype_index;
    ///
    /// newtype_index! {
    ///     struct Idx {
    ///         DEBUG_FORMAT = "idx_{}",
    ///     }
    /// }
    ///
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

    /// Skip `n` indices
    pub fn skip(&self, n: usize) {
        self.count
            .fetch_add(n, std::sync::atomic::Ordering::Relaxed);
    }
}

impl<I: Idx> Default for IndexGen<I> {
    fn default() -> Self {
        Self::new()
    }
}
