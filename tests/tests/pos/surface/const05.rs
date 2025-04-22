#![feature(adt_const_params)]
use std::marker::ConstParamTy;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, ConstParamTy)]
pub struct GasCost(pub u64);

pub struct BillyBob<const C: GasCost> {}

const GAS3: GasCost = GasCost(3);

fn test0() -> BillyBob<GAS3> {
    BillyBob {}
}
