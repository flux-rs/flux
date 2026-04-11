
use flux_attrs::*;

pub trait MyTrait {
    type A;

    #[sig(fn(_) -> MyTrait::A)] //~ ERROR ambiguous associated type
    fn f(&self) -> <Self as MyTrait>::A;
}
