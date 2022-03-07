use std::{
    convert::Infallible,
    ops::{ControlFlow, FromResidual, Try},
};

use crate::SemiGroup;

pub trait IterExt: Iterator {
    fn try_collect_exhaust<T, V, E>(self) -> Result<V, E>
    where
        E: SemiGroup,
        V: FromIterator<T>,
        Self: Iterator<Item = Result<T, E>> + Sized,
    {
        let mut acc: Option<E> = None;
        let v = ReportResiduals {
            iter: self,
            f: |residual: Result<Infallible, E>| {
                match acc.take() {
                    Some(curr) => acc = Some(curr.append(residual.unwrap_err())),
                    None => acc = Some(residual.unwrap_err()),
                }
            },
        }
        .collect();
        match acc {
            Some(e) => Err(e),
            None => Ok(v),
        }
    }

    fn try_for_each_exhaust<T, E, F>(self, mut f: F) -> Result<(), E>
    where
        Self: Iterator<Item = T> + Sized,
        E: SemiGroup,
        F: FnMut(T) -> Result<(), E>,
    {
        let mut acc: Option<E> = None;
        for v in self {
            if let Err(e) = f(v) {
                match acc.take() {
                    Some(curr) => acc = Some(curr.append(e)),
                    None => acc = Some(e),
                }
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

struct ReportResiduals<I, F> {
    iter: I,
    f: F,
}

impl<I, T, E, F, R> Iterator for ReportResiduals<I, F>
where
    I: Iterator<Item = R>,
    R: Try<Output = T, Residual = E> + FromResidual<E>,
    F: FnMut(E),
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
            match x.branch() {
                ControlFlow::Continue(x) => f(acc, x),
                ControlFlow::Break(e) => {
                    (self.f)(e);
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
