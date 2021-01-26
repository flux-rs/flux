#![feature(bindings_after_at)]
#![feature(box_syntax)]
#![feature(or_patterns)]

pub mod constraint;
pub mod env;
pub mod refineck;
pub mod region_inference;

use crate::{refineck::RefineChecker, region_inference::infer_regions};
use env::OwnershipError;
use liquid_rust_core::{ast::FnDef, freshen::NameFreshener, lower::TypeLowerer, ty::TyCtxt};
pub use liquid_rust_liquid::solver::Safeness;

#[macro_use]
extern crate liquid_rust_common;

#[macro_use]
extern crate liquid_rust_core;

pub fn check_fn_def<I, S>(func: FnDef<I, S>) -> Result<Safeness, Vec<OwnershipError>>
where
    S: Eq + Copy + std::hash::Hash,
{
    let tcx = TyCtxt::new();
    let func = NameFreshener::new(&tcx).freshen(func);
    let (conts, fn_ty) = TypeLowerer::lower_fn_def(&tcx, &func);
    let (conts, fn_ty) = infer_regions(&tcx, &func, conts, fn_ty);
    let constraint = RefineChecker::new(&tcx, &conts)
        .check_fn_def(&func, &fn_ty)?
        .lower();

    Ok(constraint.solve().unwrap().tag)
}
