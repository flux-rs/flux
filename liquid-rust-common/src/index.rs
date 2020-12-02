#[macro_export]
macro_rules! def_index {
    ($index:ident) => {
        #[repr(transparent)]
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
        pub struct $index(usize);

        unsafe impl $crate::index::Index for $index {
            fn constructor(int: usize) -> Self {
                Self(int)
            }

            fn destructor(self) -> usize {
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

    fn index_map_builder<V>(size: usize) -> IndexMapBuilder<Self, V> {
        IndexMapBuilder::new(size)
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
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

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.inner.iter().enumerate().map(|(index, value)| {
            let key = Index::constructor(index);
            (key, value)
        })
    }
}

pub struct IndexMapBuilder<K, V> {
    inner: Vec<Option<V>>,
    generator: Generator<K>,
}

impl<K: Index, V> IndexMapBuilder<K, V> {
    fn new(size: usize) -> Self {
        let mut generator = Generator::new();

        Self {
            inner: (0..size)
                .map(|_| {
                    generator.gen();
                    None
                })
                .collect(),
            generator,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = K> {
        (0..self.inner.len()).map(K::constructor)
    }

    pub fn insert(&mut self, key: K, value: V) -> bool {
        let index = key.destructor();

        if let Some(opt_value) = self.inner.get_mut(index) {
            *opt_value = Some(value);
            true
        } else {
            false
        }
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let index = key.destructor();

        self.inner.get(index).and_then(Option::as_ref)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let index = key.destructor();

        self.inner.get_mut(index).and_then(Option::as_mut)
    }

    pub fn build(self) -> Result<IndexMap<K, V>, K> {
        let inner = self
            .inner
            .into_iter()
            .enumerate()
            .map(|(index, value)| value.ok_or_else(|| K::constructor(index)))
            .collect::<Result<Vec<V>, K>>()?;

        Ok(IndexMap {
            inner,
            generator: self.generator,
        })
    }
}
