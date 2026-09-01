use std::marker::PhantomData;

pub struct InputOutput<T>(PhantomData<fn(T) -> T>);

impl<T> InputOutput<T> {
    pub fn new() -> Self {
        InputOutput::<T>(PhantomData)
    }
}
