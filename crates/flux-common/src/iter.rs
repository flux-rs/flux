use std::ops::Try;

use rustc_errors::ErrorGuaranteed;

pub trait IterExt: Iterator {
    fn try_collect_vec<T, E>(self) -> Result<Vec<T>, E>
    where
        Self: Sized + Iterator<Item = Result<T, E>>,
    {
        self.collect()
    }

    fn collect_errors<T, E, C>(self, collector: C) -> CollectErrors<Self, C>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        C: ErrorCollector<E>,
    {
        CollectErrors { iter: self, collector }
    }

    fn try_collect_exhaust<T, V>(self) -> Result<V, ErrorGuaranteed>
    where
        V: FromIterator<T>,
        Self: Iterator<Item = Result<T, ErrorGuaranteed>> + Sized,
    {
        let mut acc: Option<ErrorGuaranteed> = None;
        let v = self.collect_errors(&mut acc).collect();
        match acc {
            Some(e) => Err(e),
            None => Ok(v),
        }
    }

    fn try_for_each_exhaust<T, F>(self, mut f: F) -> Result<(), ErrorGuaranteed>
    where
        Self: Iterator<Item = T> + Sized,
        F: FnMut(T) -> Result<(), ErrorGuaranteed>,
    {
        let mut acc: Option<ErrorGuaranteed> = None;
        for v in self {
            if let Err(e) = f(v) {
                acc = Some(e).or(acc);
            }
        }
        match acc {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    fn map_take_while<F, R>(&mut self, f: F) -> MapTakeWhile<Self, F>
    where
        Self: Clone,
        F: FnMut(&Self::Item) -> Option<R>,
    {
        MapTakeWhile { iter: self, f }
    }
}

impl<I: ?Sized> IterExt for I where I: Iterator {}

pub trait ErrorCollector<E> {
    fn collect(&mut self, err: E);
}

impl<E, F> ErrorCollector<E> for F
where
    F: FnMut(E),
{
    fn collect(&mut self, err: E) {
        self(err);
    }
}

impl ErrorCollector<ErrorGuaranteed> for &mut Option<ErrorGuaranteed> {
    fn collect(&mut self, err: ErrorGuaranteed) {
        **self = Some(err).or(**self);
    }
}

pub struct CollectErrors<I, F> {
    iter: I,
    collector: F,
}

impl<I, T, E, F> Iterator for CollectErrors<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: ErrorCollector<E>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.find(|_| true)
    }

    fn try_fold<B, F2, R2>(&mut self, init: B, mut f: F2) -> R2
    where
        F2: FnMut(B, Self::Item) -> R2,
        R2: Try<Output = B>,
    {
        self.iter.try_fold(init, |acc, x| {
            match x {
                Ok(x) => f(acc, x),
                Err(e) => {
                    self.collector.collect(e);
                    try { acc }
                }
            }
        })
    }

    fn fold<B, F2>(mut self, init: B, fold: F2) -> B
    where
        Self: Sized,
        F2: FnMut(B, Self::Item) -> B,
    {
        #[inline]
        fn ok<B, T>(mut f: impl FnMut(B, T) -> B) -> impl FnMut(B, T) -> Result<B, !> {
            move |acc, x| Ok(f(acc, x))
        }

        self.try_fold(init, ok(fold)).unwrap()
    }
}

pub struct MapTakeWhile<'a, I: 'a, F> {
    iter: &'a mut I,
    f: F,
}

impl<'a, I, F, R> Iterator for MapTakeWhile<'a, I, F>
where
    I: 'a + Iterator + Clone,
    F: FnMut(&I::Item) -> Option<R>,
{
    type Item = R;

    fn next(&mut self) -> Option<Self::Item> {
        let old = self.iter.clone();
        match self.iter.next() {
            None => None,
            Some(elt) => {
                if let Some(elt) = (self.f)(&elt) {
                    Some(elt)
                } else {
                    *self.iter = old;
                    None
                }
            }
        }
    }
}
