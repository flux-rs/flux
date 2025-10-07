#![allow(unused)]

extern crate flux_core;

use flux_rs::{assert, attrs::*};

pub mod a {
    pub mod b {
        pub trait MyTrait {
            fn gromp(&self) -> usize;
        }
    }
}

pub mod x {
    pub mod y {
        pub struct Thing<T> {
            inner: T,
        }

        impl<T> Thing<T> {
            pub fn new(inner: T) -> Self {
                Thing { inner }
            }
        }

        impl<T> crate::a::b::MyTrait for Thing<T> {
            fn gromp(&self) -> usize {
                42
            }
        }
    }
}

// -------------------------------------------------------------------
mod test {
    use crate::a::b::MyTrait;

    #[flux_rs::spec(fn () -> usize[42])]
    fn test() -> usize {
        crate::x::y::Thing::new(true).gromp()
    }
}

// -------------------------------------------------------------------
#[flux_rs::specs {
    mod x {
        mod y {
            impl MyTrait for Thing<T> {
                fn gromp(&Self) -> usize[42];
            }
        }
    }
}]
const _: () = ();
