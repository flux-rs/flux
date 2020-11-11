pub struct Generator<T> {
    count: usize,
    mapper: fn(usize) -> T,
}

impl<T> Generator<T> {
    pub fn new(mapper: fn(usize) -> T) -> Self {
        Self { count: 0, mapper }
    }

    pub fn generate(&mut self) -> T {
        let t = (self.mapper)(self.count);
        self.count += 1;
        t
    }
}

pub trait Generable: Sized {
    fn generator() -> Generator<Self>;
}
