pub trait Idx: Copy + 'static + Ord + std::fmt::Debug + std::hash::Hash {
    fn new(idx: usize) -> Self;
    fn index(self) -> usize;
}

#[macro_export]
macro_rules! newtype_index {
    ($(#[$attrs:meta])* struct $index:ident) => {
        $(#[$attrs])*
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $index {
            private: usize
        }

        impl $index {
            fn from_usize(idx: usize) -> Self {
                Self {
                    private: idx
                }
            }

            fn as_usize(&self) -> usize {
                self.private
            }
        }

        impl From<usize> for $index {
            #[inline]
            fn from(value: usize) -> Self {
                Self::from_usize(value)
            }
        }

        impl $crate::index::Idx for $index {
            fn new(idx: usize) -> Self {
                Self::from_usize(idx)
            }

            fn index(self) -> usize {
                self.as_usize()
            }
        }
    };
}
