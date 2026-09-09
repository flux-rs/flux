use std::marker::PhantomData;

pub struct Unsafe<T>(PhantomData<unsafe fn(T) -> T>);

impl<T> Unsafe<T> {
    pub fn new() -> Self {
        Unsafe::<T>(PhantomData)
    }
}
