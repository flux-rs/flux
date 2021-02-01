#[macro_export]
macro_rules! newtype_name {
    ($(#[$attrs:meta])* struct $name:ident) => {
        $(#[$attrs])*
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name<T = usize> {
            private: T
        }

        impl<T> $name<T> {
            pub fn new(private: T) -> Self {
                Self { private }
            }

            pub fn inner(&self) -> &T {
                &self.private
            }
        }

        impl $name {
            pub fn as_usize(&self) -> usize {
                self.private
            }
        }

        unsafe impl $crate::index::Idx for $name {
            fn new(idx: usize) -> Self {
                Self::new(idx)
            }

            fn index(self) -> usize {
                *self.inner()
            }

            fn name() -> &'static str {
                stringify!(name)
            }
        }
    };
}

newtype_name! {
    struct MyName
}
