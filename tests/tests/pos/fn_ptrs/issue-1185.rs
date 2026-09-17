pub struct BuildHasherDefault<H>(std::marker::PhantomData<fn() -> H>);

impl<H> BuildHasherDefault<H> {
    pub fn new() -> Self {
        BuildHasherDefault::<H>(std::marker::PhantomData)
    }
}
