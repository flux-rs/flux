// Test that we can resolve sasociated type in methods

struct S<T> {
    x: T,
}

trait MyTrait {
    type Assoc;
}

impl<T> S<T> {
    fn test(&self) -> &T::Assoc
    where
        T: MyTrait,
    {
        todo!()
    }
}
