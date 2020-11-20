#[macro_export]
macro_rules! def_index {
    ($index:ident) => {
        pub struct $index(usize);

        unsafe impl $crate::index::Index for $index {
            fn constructor(int: usize) -> Self {
                Self(int)
            }

            fn destructor(self) -> Self {
                self.0
            }
        }
    };
}

pub unsafe trait Index: Sized {
    fn constructor(int: usize) -> Self;
    fn destructor(self) -> usize;

    fn first() -> Self {
        Self::constructor(0)
    }

    fn generator() -> Generator<Self> {
        Generator::new()
    }

    fn index_map<V>() -> IndexMap<Self, V> {
        IndexMap::new()
    }
}

pub struct Generator<T> {
    count: usize,
    marker: std::marker::PhantomData<T>,
}

impl<T: Index> Generator<T> {
    fn new() -> Self {
        Self {
            count: 0,
            marker: Default::default(),
        }
    }

    pub fn gen(&mut self) -> T {
        let index = self.count;
        self.count += 1;
        T::constructor(index)
    }
}

pub struct IndexMap<K, V> {
    inner: Vec<V>,
    generator: Generator<K>,
}

impl<K: Index, V> IndexMap<K, V> {
    fn new() -> Self {
        Self {
            inner: Vec::new(),
            generator: Generator::new(),
        }
    }

    pub fn insert(&mut self, value: V) -> K {
        self.inner.push(value);
        self.generator.gen()
    }

    pub fn get(&self, key: K) -> &V {
        let index = key.destructor();
        unsafe { self.inner.get_unchecked(index) }
    }

    pub fn get_mut(&mut self, key: K) -> &mut V {
        let index = key.destructor();
        unsafe { self.inner.get_unchecked_mut(index) }
    }
}
