extern crate flux_rs;

use flux_rs::*;

pub trait MyTrait {
    type A;

    #[sig(fn(_) -> MyTrait::A)] //~ ERROR ambiguous associated type
    fn f(&self) -> <Self as MyTrait>::A;
}
