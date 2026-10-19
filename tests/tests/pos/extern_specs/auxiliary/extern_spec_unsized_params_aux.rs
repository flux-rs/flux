#![feature(sized_hierarchy)]

use std::marker::{PhantomData, PointeeSized};

pub struct MaybeUnsized<T: ?Sized> {
    pub value: Box<T>,
}

impl<T: ?Sized> MaybeUnsized<T> {
    pub fn answer(&self) -> usize {
        42
    }
}

pub struct Pointee<T: PointeeSized> {
    _marker: PhantomData<T>,
}

impl<T: PointeeSized> Pointee<T> {
    pub fn answer(&self) -> usize {
        42
    }
}

pub trait Answer {
    fn answer_trait(&self) -> usize;
}

impl<T: ?Sized> Answer for MaybeUnsized<T> {
    fn answer_trait(&self) -> usize {
        42
    }
}
