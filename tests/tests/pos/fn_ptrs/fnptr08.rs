use std::marker::PhantomData;

pub struct MutableInput<T>(PhantomData<for<'a> fn(&'a mut T)>);

impl<T> MutableInput<T> {
    pub fn new() -> Self {
        MutableInput::<T>(PhantomData)
    }
}
