use std::marker::PhantomData;

pub struct MultipleBinders<T>(
    PhantomData<for<'a, 'b> fn(&'a T, &'b T) -> (&'b T, &'a T)>,
);

impl<T> MultipleBinders<T> {
    pub fn new() -> Self {
        MultipleBinders::<T>(PhantomData)
    }
}
