#[macro_export]
macro_rules! bug {
    () => {{
        unreachable!();
    }};
    ($msg:expr) => {{
        unreachable!($msg);
    }};
    ($fmt:expr, $($arg:tt)+) => ({
        unreachable!($fmt, $($arg)+);
    });
}

#[macro_export]
macro_rules! wrap_iterable {
    (@internal ($($typarams:tt),*), $constructor:ident, $outter:ty, $inner:ty, $item:ty) => {
        impl<$($typarams),*> $outter {
            pub fn iter(&self) -> <&$inner as IntoIterator>::IntoIter {
                IntoIterator::into_iter(&self.0)
            }
        }

        impl<'a,$($typarams),*> IntoIterator for &'a $outter {
            type Item = <&'a $inner as IntoIterator>::Item;

            type IntoIter = <&'a $inner as IntoIterator>::IntoIter;

            fn into_iter(self) -> Self::IntoIter {
                IntoIterator::into_iter(&self.0)
            }
        }

        impl<$($typarams),*> IntoIterator for $outter {
            type Item = <$inner as IntoIterator>::Item;

            type IntoIter = <$inner as IntoIterator>::IntoIter;

            fn into_iter(self) -> Self::IntoIter {
                IntoIterator::into_iter(self.0)
            }
        }

        impl<$($typarams),*> std::iter::FromIterator<$item> for $outter {
            fn from_iter<T: IntoIterator<Item=$item>>(iter: T) -> Self {
                $constructor(iter.into_iter().collect())
            }
        }
    };
    (for<$($params1:tt),*> $outter:ident<$($params2:tt),*> : $inner:ty) => {
        $crate::wrap_iterable! {
            @internal ($($params1),*), $outter, $outter<$($params2),*>, $inner, <$inner as IntoIterator>::Item
        }
    };
    ($outter:ident : $inner:ty) => {
        $crate::wrap_iterable! {
            @internal (), $outter, $outter, $inner, <$inner as IntoIterator>::Item
        }
    };
}

#[macro_export]
macro_rules! wrap_dict_like {
    (@internal ($($typarams:tt),*), $constructor:ident, $outter:ty, $inner:ty, $index:ty, $output:ty) => {
        impl $outter {
            pub fn get(&self, key: &$index) -> Option<&$output> {
                self.0.get(key)
            }

            pub fn keys(&self) -> impl Iterator<Item = &$index> {
                self.0.keys()
            }

            pub fn insert(&mut self, key: $index, val: $output) -> Option<$output> {
                self.0.insert(key, val)
            }
        }

        impl<'a> std::ops::Index<&'a $index> for $outter {
            type Output = <$inner as std::ops::Index<&'a $index>>::Output;

            fn index(&self, key: &'a $index) -> &Self::Output {
                self.get(key).expect(&format!("{}: key not found", std::stringify!($constructor)))
            }
        }
    };
    (for<$($params1:tt),*> $outter:ident<$($params2:tt),*>: $inner:ty {
        type Index = $index:ty;
        type Output = $output:ty;
    }) => {
        $crate::wrap_dict_like! {
            @internal ($($params1),*), $outter, $outter<$($params2),*>, $inner, $index, $output
        }
    };
    ($outter:ident: $inner:ty {
        type Index = $index:ty;
        type Output = $output:ty;
    }) => {
        $crate::wrap_dict_like! {
            @internal (), $outter, $outter, $inner, $index, $output
        }
    };
}
