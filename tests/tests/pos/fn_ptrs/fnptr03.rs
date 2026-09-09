use std::marker::PhantomData;

pub struct Input<T>(PhantomData<fn(T)>);

impl<T> Input<T> {
    pub fn new() -> Self {
        Input::<T>(PhantomData)
    }
}
