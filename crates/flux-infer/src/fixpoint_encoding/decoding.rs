use flux_middle::{
    big_int::BigInt,
    rty::{self, EarlyReftParam, InternalFuncKind, List, SpecFuncKind},
};
use flux_rustc_bridge::lowering::Lower;
use itertools::Itertools;

use super::{ConstKey, FixpointCtxt, fixpoint};

impl<'genv, 'tcx, Tag> FixpointCtxt<'genv, 'tcx, Tag>
where
    Tag: std::hash::Hash + Eq + Copy,
{
    #[expect(dead_code)]
    pub(crate) fn fixpoint_to_expr(
        &self,
        fexpr: &fixpoint::Expr,
    ) -> Result<rty::Expr, FixpointParseError> {
        match fexpr {
            fixpoint::Expr::Constant(constant) => {
                let c = match constant {
                    fixpoint::Constant::Numeral(num) => rty::Constant::Int(BigInt::from(*num)),
                    fixpoint::Constant::Real(dec) => rty::Constant::Real(rty::Real(*dec)),
                    fixpoint::Constant::Boolean(b) => rty::Constant::Bool(*b),
                    fixpoint::Constant::String(s) => rty::Constant::Str(s.0),
                    fixpoint::Constant::BitVec(bv, size) => rty::Constant::BitVec(*bv, *size),
                };
                Ok(rty::Expr::constant(c))
            }
            fixpoint::Expr::Var(fvar) => {
                match fvar {
                    fixpoint::Var::Underscore => {
                        unreachable!("Underscore should not appear in exprs")
                    }
                    fixpoint::Var::Global(global_var, _) => {
                        if let Some(const_key) = self.ecx.const_env.const_map_rev.get(global_var) {
                            match const_key {
                                ConstKey::Uif(def_id) => {
                                    Ok(rty::Expr::global_func(SpecFuncKind::Uif(*def_id)))
                                }
                                ConstKey::RustConst(def_id) => Ok(rty::Expr::const_def_id(*def_id)),
                                ConstKey::Alias(_flux_id, _args) => {
                                    unreachable!("Should be special-cased as the head of an app")
                                }
                                ConstKey::Lambda(lambda) => Ok(rty::Expr::abs(lambda.clone())),
                                ConstKey::PrimOp(bin_op) => {
                                    Ok(rty::Expr::internal_func(InternalFuncKind::Rel(
                                        bin_op.clone(),
                                    )))
                                }
                                ConstKey::Cast(_sort, _sort1) => {
                                    unreachable!(
                                        "Should be specially handled as the head of a function app."
                                    )
                                }
                            }
                        } else {
                            Err(FixpointParseError::NoGlobalVar(*global_var))
                        }
                    }
                    fixpoint::Var::Local(fname) => {
                        if let Some(var) = self.ecx.local_var_env.reverse_map.get(fname) {
                            Ok(rty::Expr::var(*var))
                        } else {
                            Err(FixpointParseError::NoLocalVar(*fname))
                        }
                    }
                    fixpoint::Var::DataCtor(adt_id, variant_idx) => {
                        let def_id = self.scx.adt_sorts[adt_id.as_usize()];
                        Ok(rty::Expr::ctor_enum(def_id, *variant_idx))
                    }
                    fixpoint::Var::TupleCtor { .. }
                    | fixpoint::Var::TupleProj { .. }
                    | fixpoint::Var::DataProj { .. }
                    | fixpoint::Var::UIFRel(_) => {
                        unreachable!(
                            "Trying to convert an atomic var, but reached a var that should only occur as the head of an app (and be special-cased in conversion as a result)"
                        )
                    }
                    fixpoint::Var::Param(EarlyReftParam { index, name }) => {
                        Ok(rty::Expr::early_param(*index, *name))
                    }
                    fixpoint::Var::ConstGeneric(const_generic) => {
                        Ok(rty::Expr::const_generic(*const_generic))
                    }
                }
            }
            fixpoint::Expr::App(fhead, fargs) => {
                match &**fhead {
                    fixpoint::Expr::Var(fixpoint::Var::TupleProj { arity, field }) => {
                        if fargs.len() == 1 {
                            let earg = self.fixpoint_to_expr(&fargs[0])?;
                            Ok(rty::Expr::field_proj(
                                earg,
                                rty::FieldProj::Tuple { arity: *arity, field: *field },
                            ))
                        } else {
                            Err(FixpointParseError::ProjArityMismatch(fargs.len()))
                        }
                    }
                    fixpoint::Expr::Var(fixpoint::Var::DataProj { adt_id, field }) => {
                        if fargs.len() == 1 {
                            let earg = self.fixpoint_to_expr(&fargs[0])?;
                            Ok(rty::Expr::field_proj(
                                earg,
                                rty::FieldProj::Adt {
                                    def_id: self.scx.adt_sorts[adt_id.as_usize()],
                                    field: *field,
                                },
                            ))
                        } else {
                            Err(FixpointParseError::ProjArityMismatch(fargs.len()))
                        }
                    }
                    fixpoint::Expr::Var(fixpoint::Var::TupleCtor { arity }) => {
                        if fargs.len() == *arity {
                            let eargs = fargs
                                .iter()
                                .map(|farg| self.fixpoint_to_expr(farg))
                                .try_collect()?;
                            Ok(rty::Expr::tuple(eargs))
                        } else {
                            Err(FixpointParseError::TupleCtorArityMismatch(*arity, fargs.len()))
                        }
                    }
                    fixpoint::Expr::Var(fixpoint::Var::UIFRel(fbinrel)) => {
                        if fargs.len() == 2 {
                            let e1 = self.fixpoint_to_expr(&fargs[0])?;
                            let e2 = self.fixpoint_to_expr(&fargs[1])?;
                            let binrel = match fbinrel {
                                fixpoint::BinRel::Eq => rty::BinOp::Eq,
                                fixpoint::BinRel::Ne => rty::BinOp::Ne,
                                // FIXME: (ck) faked sort information
                                //
                                // This needs to be a sort that goes to the UIFRel
                                // case in fixpoint conversion. Again, if we actually
                                // need to inspect the sorts this will die unless the
                                // arguments are actually Strs.
                                fixpoint::BinRel::Gt => rty::BinOp::Gt(rty::Sort::Str),
                                fixpoint::BinRel::Ge => rty::BinOp::Ge(rty::Sort::Str),
                                fixpoint::BinRel::Lt => rty::BinOp::Lt(rty::Sort::Str),
                                fixpoint::BinRel::Le => rty::BinOp::Le(rty::Sort::Str),
                            };
                            Ok(rty::Expr::binary_op(binrel, e1, e2))
                        } else {
                            Err(FixpointParseError::UIFRelArityMismatch(fargs.len()))
                        }
                    }
                    fixpoint::Expr::Var(fixpoint::Var::Global(global_var, _)) => {
                        if let Some(const_key) = self.ecx.const_env.const_map_rev.get(global_var) {
                            match const_key {
                                // NOTE: Only a few of these are meaningfully needed,
                                // e.g. ConstKey::Alias because the rty Expr has its
                                // args as a part of it.
                                ConstKey::PrimOp(bin_op) => {
                                    if fargs.len() != 2 {
                                        Err(FixpointParseError::PrimOpArityMismatch(fargs.len()))
                                    } else {
                                        Ok(rty::Expr::prim_val(
                                            bin_op.clone(),
                                            self.fixpoint_to_expr(&fargs[0])?,
                                            self.fixpoint_to_expr(&fargs[1])?,
                                        ))
                                    }
                                }
                                ConstKey::Cast(sort1, sort2) => {
                                    if fargs.len() != 1 {
                                        Err(FixpointParseError::CastArityMismatch(fargs.len()))
                                    } else {
                                        Ok(rty::Expr::cast(
                                            sort1.clone(),
                                            sort2.clone(),
                                            self.fixpoint_to_expr(&fargs[0])?,
                                        ))
                                    }
                                }
                                ConstKey::Alias(assoc_id, generic_args) => {
                                    let lowered_args: flux_rustc_bridge::ty::GenericArgs =
                                        generic_args.lower(self.genv.tcx()).unwrap();
                                    let generic_args = rty::refining::Refiner::default_for_item(
                                        self.genv,
                                        assoc_id.parent(),
                                    )
                                    .unwrap()
                                    .refine_generic_args(assoc_id.parent(), &lowered_args)
                                    .unwrap();
                                    let alias_reft =
                                        rty::AliasReft { assoc_id: *assoc_id, args: generic_args };
                                    let args = fargs
                                        .iter()
                                        .map(|farg| self.fixpoint_to_expr(farg))
                                        .try_collect()?;
                                    Ok(rty::Expr::alias(alias_reft, args))
                                }
                                ConstKey::Uif(..)
                                | ConstKey::RustConst(..)
                                | ConstKey::Lambda(..) => {
                                    // These should be treated as a normal app.
                                    self.fixpoint_app_to_expr(fhead, fargs)
                                }
                            }
                        } else {
                            Err(FixpointParseError::NoGlobalVar(*global_var))
                        }
                    }
                    fhead => self.fixpoint_app_to_expr(fhead, fargs),
                }
            }
            fixpoint::Expr::Neg(fexpr) => {
                let e = self.fixpoint_to_expr(fexpr)?;
                Ok(rty::Expr::neg(&e))
            }
            fixpoint::Expr::BinaryOp(fbinop, boxed_args) => {
                let binop = match fbinop {
                    // FIXME: (ck) faked sort information
                    //
                    // See what we do for binrel for an explanation.
                    fixpoint::BinOp::Add => rty::BinOp::Add(rty::Sort::Int),
                    fixpoint::BinOp::Sub => rty::BinOp::Sub(rty::Sort::Int),
                    fixpoint::BinOp::Mul => rty::BinOp::Mul(rty::Sort::Int),
                    fixpoint::BinOp::Div => rty::BinOp::Div(rty::Sort::Int),
                    fixpoint::BinOp::Mod => rty::BinOp::Mod(rty::Sort::Int),
                };
                let [fe1, fe2] = &**boxed_args;
                let e1 = self.fixpoint_to_expr(fe1)?;
                let e2 = self.fixpoint_to_expr(fe2)?;
                Ok(rty::Expr::binary_op(binop, e1, e2))
            }
            fixpoint::Expr::IfThenElse(boxed_args) => {
                let [fe1, fe2, fe3] = &**boxed_args;
                let e1 = self.fixpoint_to_expr(fe1)?;
                let e2 = self.fixpoint_to_expr(fe2)?;
                let e3 = self.fixpoint_to_expr(fe3)?;
                Ok(rty::Expr::ite(e1, e2, e3))
            }
            fixpoint::Expr::And(fexprs) => {
                let exprs: Vec<rty::Expr> = fexprs
                    .iter()
                    .map(|fexpr| self.fixpoint_to_expr(fexpr))
                    .try_collect()?;
                Ok(rty::Expr::and_from_iter(exprs))
            }
            fixpoint::Expr::Or(fexprs) => {
                let exprs: Vec<rty::Expr> = fexprs
                    .iter()
                    .map(|fexpr| self.fixpoint_to_expr(fexpr))
                    .try_collect()?;
                Ok(rty::Expr::or_from_iter(exprs))
            }
            fixpoint::Expr::Not(fexpr) => {
                let e = self.fixpoint_to_expr(fexpr)?;
                Ok(rty::Expr::not(&e))
            }
            fixpoint::Expr::Imp(boxed_args) => {
                let [fe1, fe2] = &**boxed_args;
                let e1 = self.fixpoint_to_expr(fe1)?;
                let e2 = self.fixpoint_to_expr(fe2)?;
                Ok(rty::Expr::binary_op(rty::BinOp::Imp, e1, e2))
            }
            fixpoint::Expr::Iff(boxed_args) => {
                let [fe1, fe2] = &**boxed_args;
                let e1 = self.fixpoint_to_expr(fe1)?;
                let e2 = self.fixpoint_to_expr(fe2)?;
                Ok(rty::Expr::binary_op(rty::BinOp::Iff, e1, e2))
            }
            fixpoint::Expr::Atom(fbinrel, boxed_args) => {
                let binrel = match fbinrel {
                    fixpoint::BinRel::Eq => rty::BinOp::Eq,
                    fixpoint::BinRel::Ne => rty::BinOp::Ne,
                    // FIXME: (ck) faked sort information
                    //
                    // I'm pretty sure that it is OK to give `rty::Sort::Int`
                    // because we only emit `fixpoint::BinRel::Gt`, etc. when we
                    // have an Int/Real/Char sort (and further this sort info
                    // isn't further used). But if we inspect this in other
                    // places then things could break.
                    fixpoint::BinRel::Gt => rty::BinOp::Gt(rty::Sort::Int),
                    fixpoint::BinRel::Ge => rty::BinOp::Ge(rty::Sort::Int),
                    fixpoint::BinRel::Lt => rty::BinOp::Lt(rty::Sort::Int),
                    fixpoint::BinRel::Le => rty::BinOp::Le(rty::Sort::Int),
                };
                let [fe1, fe2] = &**boxed_args;
                let e1 = self.fixpoint_to_expr(fe1)?;
                let e2 = self.fixpoint_to_expr(fe2)?;
                Ok(rty::Expr::binary_op(binrel, e1, e2))
            }
            fixpoint::Expr::Let(_var, _boxed_args) => {
                // TODO: (ck) uncomment this and fix the missing code in the todo!()
                //
                // let [fe1, fe2] = &**boxed_args;
                // let e1 = self.fixpoint_to_expr(fe1)?;
                // let e2 = self.fixpoint_to_expr(fe2)?;
                // let e2_binder =
                todo!("Convert `var` in e2 to locally nameless var, then fill in sort");
                // Ok(rty::Expr::let_(e1, e2_binder))
            }
            fixpoint::Expr::ThyFunc(itf) => Ok(rty::Expr::global_func(SpecFuncKind::Thy(*itf))),
            fixpoint::Expr::IsCtor(var, fe) => {
                let (def_id, variant_idx) = match var {
                    fixpoint::Var::DataCtor(adt_id, variant_idx) => {
                        let def_id = self.scx.adt_sorts[adt_id.as_usize()];
                        Ok((def_id, *variant_idx))
                    }
                    _ => Err(FixpointParseError::WrongVarInIsCtor(*var)),
                }?;
                let e = self.fixpoint_to_expr(fe)?;
                Ok(rty::Expr::is_ctor(def_id, variant_idx, e))
            }
        }
    }

    #[expect(dead_code)]
    fn fixpoint_app_to_expr(
        &self,
        fhead: &fixpoint::Expr,
        fargs: &[fixpoint::Expr],
    ) -> Result<rty::Expr, FixpointParseError> {
        let head = self.fixpoint_to_expr(fhead)?;
        let args = fargs
            .iter()
            .map(|farg| self.fixpoint_to_expr(farg))
            .try_collect()?;
        Ok(rty::Expr::app(head, List::empty(), args))
    }
}

#[derive(Debug)]
pub enum FixpointParseError {
    /// UIFRels are encoded as Apps, but they are as of right now only binary
    /// relations so they must have 2 arguments only.
    UIFRelArityMismatch(usize),
    /// Expected arity (based off of the tuple ctor), actual arity (the numer of args)
    TupleCtorArityMismatch(usize, usize),
    /// The number of arguments should only ever be 1 for a tuple proj
    ProjArityMismatch(usize),
    NoGlobalVar(fixpoint::GlobalVar),
    /// Casts should only have 1 arg
    CastArityMismatch(usize),
    PrimOpArityMismatch(usize),
    NoLocalVar(fixpoint::LocalVar),
    /// Expecting fixpoint::Var::DataCtor
    WrongVarInIsCtor(fixpoint::Var),
}
