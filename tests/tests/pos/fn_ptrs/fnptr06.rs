use std::marker::PhantomData;

pub struct HigherRanked<T>(PhantomData<for<'a> fn(&'a T) -> &'a T>);

impl<T> HigherRanked<T> {
    pub fn new() -> Self {
        HigherRanked::<T>(PhantomData)
    }
}
