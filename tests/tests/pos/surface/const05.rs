#![feature(adt_const_params)]
use std::marker::ConstParamTy;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, ConstParamTy)]
pub struct GasCost(pub u64);

// impl GasCost {
//     pub const fn as_value(&self) -> u64 {
//         self.0
//     }
// }

pub struct BillyBob<const C: GasCost> {}

const GAS3: GasCost = GasCost(3);

fn mk() -> BillyBob<GAS3> {
    BillyBob {}
}

// impl<const C: GasCost> BillyBob<C> {
//     pub fn value(&self) -> u64 {
//         C.as_value()
//     }
// }

// pub fn test1<const C: GasCost>() -> u64 {
//     12
// }

// pub fn test2<const C: GasCost>() -> u64 {
//     test1::<C>()
// }

// pub fn test3<const C: GasCost>(b: BillyBob<C>) -> u64 {
//     b.value()
//     // test1::<C>()
// }
