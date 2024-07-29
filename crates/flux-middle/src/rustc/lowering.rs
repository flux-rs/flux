use flux_common::result::ResultExt;
use flux_errors::FluxSession;
use itertools::Itertools;
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_infer::{infer::TyCtxtInferExt, traits::Obligation};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::{
    mir::{self as rustc_mir, ConstValue},
    traits::{ImplSource, ObligationCause},
    ty::{
        self as rustc_ty, adjustment as rustc_adjustment, GenericArgKind, ParamConst, ParamEnv,
        TyCtxt, ValTree,
    },
};
use rustc_span::{def_id::LocalDefId, Span};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    mir::{
        replicate_infer_ctxt, AggregateKind, AssertKind, BasicBlockData, BinOp, Body, BorrowKind,
        CallArgs, CastKind, Constant, FakeReadCause, LocalDecl, Operand, Place, PlaceElem,
        PointerCast, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AdtDef, AdtDefData, AliasKind, Binder, BoundRegion, BoundVariableKind, Clause, ClauseKind,
        Const, ConstKind, ExistentialPredicate, FieldDef, FnSig, GenericArg, GenericParamDef,
        GenericParamDefKind, GenericPredicates, Generics, OutlivesPredicate, PolyFnSig,
        TraitPredicate, TraitRef, Ty, TypeOutlivesPredicate, VariantDef,
    },
};
use crate::{
    const_eval::scalar_int_to_constant,
    intern::List,
    rustc::ty::{AliasTy, ExistentialTraitRef, ProjectionPredicate, Region},
};

pub struct LoweringCtxt<'a, 'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    selcx: SelectionContext<'a, 'tcx>,
    sess: &'sess FluxSession,
    rustc_mir: &'a rustc_mir::Body<'tcx>,
}

#[derive(Debug, Clone)]
pub struct UnsupportedReason {
    pub(crate) descr: String,
}

impl UnsupportedReason {
    fn new(reason: impl ToString) -> Self {
        UnsupportedReason { descr: reason.to_string() }
    }

    pub fn into_err(self) -> UnsupportedErr {
        UnsupportedErr { descr: self.descr, span: None }
    }
}

#[derive(Debug, Clone, Encodable, Decodable)]
pub struct UnsupportedErr {
    pub descr: String,
    pub(crate) span: Option<Span>,
}

impl UnsupportedErr {
    pub fn new(reason: UnsupportedReason) -> Self {
        UnsupportedErr { descr: reason.descr, span: None }
    }

    fn with_span(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }
}

fn trait_ref_impl_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    selcx: &mut SelectionContext<'_, 'tcx>,
    param_env: ParamEnv<'tcx>,
    trait_ref: rustc_ty::TraitRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let obligation = Obligation::new(tcx, ObligationCause::dummy(), param_env, trait_ref);
    let impl_source = selcx.select(&obligation).ok()??;
    let impl_source = selcx.infcx.resolve_vars_if_possible(impl_source);
    let ImplSource::UserDefined(impl_data) = impl_source else {
        return None;
    };
    Some((impl_data.impl_def_id, impl_data.args))
}

pub fn resolve_trait_ref_impl_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    trait_ref: rustc_ty::TraitRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let param_env = tcx.param_env(def_id.to_def_id());
    let infcx = tcx.infer_ctxt().build();
    trait_ref_impl_id(tcx, &mut SelectionContext::new(&infcx), param_env, trait_ref)
}

fn resolve_call_query<'tcx>(
    tcx: TyCtxt<'tcx>,
    selcx: &mut SelectionContext<'_, 'tcx>,
    param_env: ParamEnv<'tcx>,
    callee_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let trait_id = tcx.trait_of_item(callee_id)?;
    let trait_ref = rustc_ty::TraitRef::from_method(tcx, trait_id, args);
    let (impl_def_id, impl_args) = trait_ref_impl_id(tcx, selcx, param_env, trait_ref)?;
    let impl_args = args.rebase_onto(tcx, trait_id, impl_args);
    let assoc_id = tcx.impl_item_implementor_ids(impl_def_id).get(&callee_id)?;
    let assoc_item = tcx.associated_item(assoc_id);
    Some((assoc_item.def_id, impl_args))
}

pub fn resolve_call_from<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_id: LocalDefId,
    callee_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let param_env = tcx.param_env(caller_id.to_def_id());
    let infcx = tcx.infer_ctxt().build();
    resolve_call_query(tcx, &mut SelectionContext::new(&infcx), param_env, callee_id, args)
}

impl<'sess, 'tcx> LoweringCtxt<'_, 'sess, 'tcx> {
    pub fn lower_mir_body(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) -> Result<Body<'tcx>, ErrorGuaranteed> {
        let infcx = replicate_infer_ctxt(tcx, &body_with_facts);
        let param_env = tcx.param_env(body_with_facts.body.source.def_id());
        let selcx = SelectionContext::new(&infcx);
        let mut lower =
            LoweringCtxt { tcx, selcx, param_env, sess, rustc_mir: &body_with_facts.body };

        let basic_blocks = lower
            .rustc_mir
            .basic_blocks
            .iter()
            .map(|bb_data| lower.lower_basic_block_data(bb_data))
            .try_collect()?;

        let local_decls = lower
            .rustc_mir
            .local_decls
            .iter()
            .map(|local_decl| lower.lower_local_decl(local_decl))
            .try_collect()?;

        let body = Body::new(basic_blocks, local_decls, body_with_facts, infcx);
        Ok(body)
    }

    fn lower_basic_block_data(
        &mut self,
        data: &rustc_mir::BasicBlockData<'tcx>,
    ) -> Result<BasicBlockData<'tcx>, ErrorGuaranteed> {
        let data = BasicBlockData {
            statements: data
                .statements
                .iter()
                .map(|stmt| self.lower_statement(stmt))
                .try_collect()?,
            terminator: data
                .terminator
                .as_ref()
                .map(|terminator| self.lower_terminator(terminator))
                .transpose()?,
            is_cleanup: data.is_cleanup,
        };
        Ok(data)
    }

    fn lower_local_decl(
        &self,
        local_decl: &rustc_mir::LocalDecl<'tcx>,
    ) -> Result<LocalDecl, ErrorGuaranteed> {
        Ok(LocalDecl {
            ty: lower_ty(self.tcx, local_decl.ty)
                .map_err(|err| errors::UnsupportedLocalDecl::new(local_decl, err))
                .emit(self.sess)?,
            source_info: local_decl.source_info,
        })
    }

    fn lower_statement(
        &self,
        stmt: &rustc_mir::Statement<'tcx>,
    ) -> Result<Statement, ErrorGuaranteed> {
        let span = stmt.source_info.span;
        let kind = match &stmt.kind {
            rustc_mir::StatementKind::Assign(box (place, rvalue)) => {
                StatementKind::Assign(
                    lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    self.lower_rvalue(rvalue)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )
            }
            rustc_mir::StatementKind::SetDiscriminant { place, variant_index } => {
                StatementKind::SetDiscriminant(
                    lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    *variant_index,
                )
            }
            rustc_mir::StatementKind::FakeRead(box (cause, place)) => {
                StatementKind::FakeRead(Box::new((
                    self.lower_fake_read_cause(*cause)
                        .ok_or_else(|| errors::UnsupportedMir::from(stmt))
                        .emit(self.sess)?,
                    lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )))
            }
            rustc_mir::StatementKind::PlaceMention(place) => {
                StatementKind::PlaceMention(
                    lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )
            }
            rustc_mir::StatementKind::Nop
            | rustc_mir::StatementKind::StorageLive(_)
            | rustc_mir::StatementKind::StorageDead(_) => StatementKind::Nop,
            rustc_mir::StatementKind::AscribeUserType(
                box (place, rustc_mir::UserTypeProjection { projs, .. }),
                variance,
            ) if projs.is_empty() => {
                StatementKind::AscribeUserType(
                    lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    *variance,
                )
            }
            rustc_mir::StatementKind::Retag(_, _)
            | rustc_mir::StatementKind::Deinit(_)
            | rustc_mir::StatementKind::AscribeUserType(..)
            | rustc_mir::StatementKind::Coverage(_)
            | rustc_mir::StatementKind::Intrinsic(_)
            | rustc_mir::StatementKind::ConstEvalCounter => {
                return Err(errors::UnsupportedMir::from(stmt)).emit(self.sess);
            }
        };
        Ok(Statement { kind, source_info: stmt.source_info })
    }

    fn lower_fake_read_cause(&self, cause: rustc_mir::FakeReadCause) -> Option<FakeReadCause> {
        match cause {
            rustc_mir::FakeReadCause::ForLet(def_id) => Some(FakeReadCause::ForLet(def_id)),
            rustc_mir::FakeReadCause::ForMatchedPlace(def_id) => {
                Some(FakeReadCause::ForMatchedPlace(def_id))
            }
            rustc_mir::FakeReadCause::ForMatchGuard
            | rustc_mir::FakeReadCause::ForGuardBinding
            | rustc_mir::FakeReadCause::ForIndex { .. } => None,
        }
    }

    fn lower_terminator(
        &mut self,
        terminator: &rustc_mir::Terminator<'tcx>,
    ) -> Result<Terminator<'tcx>, ErrorGuaranteed> {
        let span = terminator.source_info.span;
        let kind = match &terminator.kind {
            rustc_mir::TerminatorKind::Return => TerminatorKind::Return,
            rustc_mir::TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
                let (func, generic_args) = match func.ty(self.rustc_mir, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, args) => {
                        let lowered = lower_generic_args(self.tcx, args)
                            .map_err(|_err| errors::UnsupportedMir::from(terminator))
                            .emit(self.sess)?;
                        (*fn_def, CallArgs { orig: args, lowered })
                    }
                    _ => Err(errors::UnsupportedMir::from(terminator)).emit(self.sess)?,
                };

                let destination = lower_place(destination)
                    .map_err(|reason| {
                        errors::UnsupportedMir::new(span, "terminator destination", reason)
                    })
                    .emit(self.sess)?;

                let resolved_call = self
                    .resolve_call(func, generic_args.orig)
                    .map_err(|reason| errors::UnsupportedMir::new(span, "terminator call", reason))
                    .emit(self.sess)?;

                TerminatorKind::Call {
                    func,
                    generic_args,
                    destination,
                    target: *target,
                    args: args
                        .iter()
                        .map(|arg| {
                            self.lower_operand(&arg.node).map_err(|reason| {
                                errors::UnsupportedMir::new(span, "terminator args", reason)
                            })
                        })
                        .try_collect()
                        .emit(self.sess)?,
                    unwind: *unwind,
                    resolved_call,
                }
            }
            rustc_mir::TerminatorKind::SwitchInt { discr, targets, .. } => {
                TerminatorKind::SwitchInt {
                    discr: self
                        .lower_operand(discr)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    targets: targets.clone(),
                }
            }
            rustc_mir::TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
            rustc_mir::TerminatorKind::Drop { place, target, unwind, .. } => {
                TerminatorKind::Drop {
                    place: lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    target: *target,
                    unwind: *unwind,
                }
            }
            rustc_mir::TerminatorKind::Assert { cond, target, expected, msg, .. } => {
                TerminatorKind::Assert {
                    cond: self
                        .lower_operand(cond)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    expected: *expected,
                    target: *target,
                    msg: self
                        .lower_assert_msg(msg)
                        .ok_or_else(|| errors::UnsupportedMir::from(terminator))
                        .emit(self.sess)?,
                }
            }
            rustc_mir::TerminatorKind::Unreachable => TerminatorKind::Unreachable,
            rustc_mir::TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                TerminatorKind::FalseEdge {
                    real_target: *real_target,
                    imaginary_target: *imaginary_target,
                }
            }
            rustc_mir::TerminatorKind::FalseUnwind { real_target, unwind } => {
                TerminatorKind::FalseUnwind { real_target: *real_target, unwind: *unwind }
            }
            rustc_mir::TerminatorKind::Yield { value, resume, resume_arg, drop } => {
                TerminatorKind::Yield {
                    value: self
                        .lower_operand(value)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    resume: *resume,
                    resume_arg: lower_place(resume_arg)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    drop: *drop,
                }
            }
            rustc_mir::TerminatorKind::CoroutineDrop => TerminatorKind::CoroutineDrop,
            rustc_mir::TerminatorKind::UnwindResume => TerminatorKind::UnwindResume,
            rustc_mir::TerminatorKind::UnwindTerminate(..)
            | rustc_mir::TerminatorKind::InlineAsm { .. } => {
                return Err(errors::UnsupportedMir::from(terminator)).emit(self.sess);
            }
        };
        Ok(Terminator { kind, source_info: terminator.source_info })
    }

    fn resolve_call(
        &mut self,
        callee_id: DefId,
        args: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Result<(DefId, CallArgs<'tcx>), UnsupportedReason> {
        let (resolved_id, resolved_args) =
            resolve_call_query(self.tcx, &mut self.selcx, self.param_env, callee_id, args)
                .unwrap_or((callee_id, args));
        let call_args =
            CallArgs { lowered: lower_generic_args(self.tcx, resolved_args)?, orig: resolved_args };
        Ok((resolved_id, call_args))
    }

    fn lower_rvalue(&self, rvalue: &rustc_mir::Rvalue<'tcx>) -> Result<Rvalue, UnsupportedReason> {
        match rvalue {
            rustc_mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            rustc_mir::Rvalue::BinaryOp(bin_op, box (op1, op2)) => {
                Ok(Rvalue::BinaryOp(
                    self.lower_bin_op(*bin_op)?,
                    self.lower_operand(op1)?,
                    self.lower_operand(op2)?,
                ))
            }
            rustc_mir::Rvalue::Ref(region, bk, p) => {
                Ok(Rvalue::Ref(
                    lower_region(region)?,
                    self.lower_borrow_kind(*bk)?,
                    lower_place(p)?,
                ))
            }
            rustc_mir::Rvalue::UnaryOp(un_op, op) => {
                Ok(Rvalue::UnaryOp(*un_op, self.lower_operand(op)?))
            }
            rustc_mir::Rvalue::Aggregate(aggregate_kind, args) => {
                let aggregate_kind = self.lower_aggregate_kind(aggregate_kind)?;
                let args = args.iter().map(|op| self.lower_operand(op)).try_collect()?;
                Ok(Rvalue::Aggregate(aggregate_kind, args))
            }
            rustc_mir::Rvalue::Discriminant(p) => Ok(Rvalue::Discriminant(lower_place(p)?)),
            rustc_mir::Rvalue::Len(place) => Ok(Rvalue::Len(lower_place(place)?)),
            rustc_mir::Rvalue::Cast(kind, op, ty) => {
                let kind = self.lower_cast_kind(*kind).ok_or_else(|| {
                    UnsupportedReason::new(format!("unsupported cast `{kind:?}`"))
                })?;
                let op = self.lower_operand(op)?;
                let ty = lower_ty(self.tcx, *ty)?;
                Ok(Rvalue::Cast(kind, op, ty))
            }
            rustc_mir::Rvalue::Repeat(op, c) => {
                let op = self.lower_operand(op)?;
                let c = lower_const(self.tcx, *c)?;
                Ok(Rvalue::Repeat(op, c))
            }
            rustc_mir::Rvalue::ThreadLocalRef(_)
            | rustc_mir::Rvalue::AddressOf(_, _)
            | rustc_mir::Rvalue::NullaryOp(_, _)
            | rustc_mir::Rvalue::CopyForDeref(_)
            | rustc_mir::Rvalue::ShallowInitBox(_, _) => {
                Err(UnsupportedReason::new(format!("unsupported rvalue `{rvalue:?}`")))
            }
        }
    }

    fn lower_borrow_kind(
        &self,
        bk: rustc_mir::BorrowKind,
    ) -> Result<BorrowKind, UnsupportedReason> {
        match bk {
            rustc_mir::BorrowKind::Shared => Ok(BorrowKind::Shared),
            rustc_mir::BorrowKind::Mut { kind } => Ok(BorrowKind::Mut { kind }),
            rustc_mir::BorrowKind::Fake(_) => {
                Err(UnsupportedReason::new(format!("unsupported borrow kind `{bk:?}`")))
            }
        }
    }

    fn lower_pointer_coercion(
        &self,
        coercion: rustc_adjustment::PointerCoercion,
    ) -> Option<PointerCast> {
        match coercion {
            rustc_adjustment::PointerCoercion::MutToConstPointer => {
                Some(crate::rustc::mir::PointerCast::MutToConstPointer)
            }
            rustc_adjustment::PointerCoercion::Unsize => {
                Some(crate::rustc::mir::PointerCast::Unsize)
            }
            _ => None,
        }
    }
    fn lower_cast_kind(&self, kind: rustc_mir::CastKind) -> Option<CastKind> {
        match kind {
            rustc_mir::CastKind::IntToInt => Some(CastKind::IntToInt),
            rustc_mir::CastKind::IntToFloat => Some(CastKind::IntToFloat),
            rustc_mir::CastKind::FloatToInt => Some(CastKind::FloatToInt),
            rustc_mir::CastKind::PtrToPtr => Some(CastKind::PtrToPtr),
            rustc_mir::CastKind::PointerCoercion(ptr_coercion) => {
                Some(CastKind::Pointer(self.lower_pointer_coercion(ptr_coercion)?))
            }
            rustc_mir::CastKind::PointerExposeProvenance => Some(CastKind::PointerExposeProvenance),
            rustc_mir::CastKind::PointerWithExposedProvenance => {
                Some(CastKind::PointerWithExposedProvenance)
            }
            _ => None,
        }
    }

    fn lower_aggregate_kind(
        &self,
        aggregate_kind: &rustc_mir::AggregateKind<'tcx>,
    ) -> Result<AggregateKind, UnsupportedReason> {
        match aggregate_kind {
            rustc_mir::AggregateKind::Adt(def_id, variant_idx, args, None, None) => {
                Ok(AggregateKind::Adt(*def_id, *variant_idx, lower_generic_args(self.tcx, args)?))
            }
            rustc_mir::AggregateKind::Array(ty) => {
                Ok(AggregateKind::Array(lower_ty(self.tcx, *ty)?))
            }
            rustc_mir::AggregateKind::Tuple => Ok(AggregateKind::Tuple),
            rustc_mir::AggregateKind::Closure(did, args) => {
                let args = lower_generic_args(self.tcx, args)?;
                Ok(AggregateKind::Closure(*did, args))
            }
            rustc_mir::AggregateKind::Coroutine(did, args) => {
                let args = lower_generic_args(self.tcx, args)?;
                Ok(AggregateKind::Coroutine(*did, args))
            }
            rustc_mir::AggregateKind::RawPtr(_, _)
            | rustc_mir::AggregateKind::Adt(..)
            | rustc_mir::AggregateKind::CoroutineClosure(..) => {
                Err(UnsupportedReason::new(format!(
                    "unsupported aggregate kind `{aggregate_kind:?}`"
                )))
            }
        }
    }

    fn lower_bin_op(&self, bin_op: rustc_mir::BinOp) -> Result<BinOp, UnsupportedReason> {
        match bin_op {
            rustc_mir::BinOp::Add => Ok(BinOp::Add),
            rustc_mir::BinOp::Sub => Ok(BinOp::Sub),
            rustc_mir::BinOp::Gt => Ok(BinOp::Gt),
            rustc_mir::BinOp::Ge => Ok(BinOp::Ge),
            rustc_mir::BinOp::Lt => Ok(BinOp::Lt),
            rustc_mir::BinOp::Le => Ok(BinOp::Le),
            rustc_mir::BinOp::Eq => Ok(BinOp::Eq),
            rustc_mir::BinOp::Ne => Ok(BinOp::Ne),
            rustc_mir::BinOp::Mul => Ok(BinOp::Mul),
            rustc_mir::BinOp::Div => Ok(BinOp::Div),
            rustc_mir::BinOp::Rem => Ok(BinOp::Rem),
            rustc_mir::BinOp::BitAnd => Ok(BinOp::BitAnd),
            rustc_mir::BinOp::BitOr => Ok(BinOp::BitOr),
            rustc_mir::BinOp::BitXor => Ok(BinOp::BitXor),
            rustc_mir::BinOp::Shl => Ok(BinOp::Shl),
            rustc_mir::BinOp::Shr => Ok(BinOp::Shr),
            rustc_mir::BinOp::AddUnchecked
            | rustc_mir::BinOp::SubUnchecked
            | rustc_mir::BinOp::MulUnchecked
            | rustc_mir::BinOp::ShlUnchecked
            | rustc_mir::BinOp::ShrUnchecked
            | rustc_mir::BinOp::AddWithOverflow
            | rustc_mir::BinOp::SubWithOverflow
            | rustc_mir::BinOp::MulWithOverflow
            | rustc_mir::BinOp::Cmp
            | rustc_mir::BinOp::Offset => {
                Err(UnsupportedReason::new(format!("unsupported binary op `{bin_op:?}`")))
            }
        }
    }

    fn lower_operand(&self, op: &rustc_mir::Operand<'tcx>) -> Result<Operand, UnsupportedReason> {
        match op {
            rustc_mir::Operand::Copy(place) => Ok(Operand::Copy(lower_place(place)?)),
            rustc_mir::Operand::Move(place) => Ok(Operand::Move(lower_place(place)?)),
            rustc_mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
        }
    }

    fn lower_constant(
        &self,
        constant: &rustc_mir::ConstOperand<'tcx>,
    ) -> Result<Constant, UnsupportedReason> {
        use rustc_middle::ty::TyKind;
        use rustc_mir::{interpret::Scalar, Const};
        let tcx = self.tcx;

        // HACK(nilehmann) we evaluate the constant to support u32::MAX
        // we should instead lower it as is and refine its type.
        let val = constant.const_.normalize(tcx, ParamEnv::empty());
        let ty = constant.ty();
        match (val, ty.kind()) {
            (Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), ty), _) => {
                scalar_int_to_constant(tcx, scalar, ty)
            }
            (Const::Val(ConstValue::Slice { .. }, _), TyKind::Ref(_, ref_ty, _))
                if ref_ty.is_str() =>
            {
                Some(Constant::Str)
            }
            (Const::Ty(ty, c), _) => {
                match c.kind() {
                    rustc_ty::ConstKind::Value(ty, rustc_ty::ValTree::Leaf(scalar)) => {
                        scalar_int_to_constant(tcx, scalar, ty)
                    }
                    rustc_ty::ConstKind::Param(param_const) => {
                        let ty = lower_ty(tcx, ty)?;
                        Some(Constant::Param(param_const, ty))
                    }
                    _ => None,
                }
            }
            (_, TyKind::Tuple(tys)) if tys.is_empty() => return Ok(Constant::Unit),
            (_, _) => Some(Constant::Opaque(lower_ty(tcx, ty)?)),
        }
        .ok_or_else(|| UnsupportedReason::new(format!("unsupported constant `{constant:?}`")))
    }

    fn lower_assert_msg(&self, msg: &rustc_mir::AssertMessage) -> Option<AssertKind> {
        use rustc_mir::AssertKind::*;
        match msg {
            BoundsCheck { .. } => Some(AssertKind::BoundsCheck),
            DivisionByZero(_) => Some(AssertKind::DivisionByZero),
            RemainderByZero(_) => Some(AssertKind::RemainderByZero),
            Overflow(bin_op, ..) => Some(AssertKind::Overflow(self.lower_bin_op(*bin_op).ok()?)),
            _ => None,
        }
    }
}

pub fn lower_place(place: &rustc_mir::Place) -> Result<Place, UnsupportedReason> {
    let mut projection = vec![];
    for elem in place.projection {
        match elem {
            rustc_mir::PlaceElem::Deref => projection.push(PlaceElem::Deref),
            rustc_mir::PlaceElem::Field(field, _) => projection.push(PlaceElem::Field(field)),
            rustc_mir::PlaceElem::Downcast(name, idx) => {
                projection.push(PlaceElem::Downcast(name, idx));
            }
            rustc_mir::PlaceElem::Index(v) => projection.push(PlaceElem::Index(v)),
            _ => {
                return Err(UnsupportedReason::new(format!("unsupported place `{place:?}`")));
            }
        }
    }
    Ok(Place { local: place.local, projection })
}

pub fn lower_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_sig: rustc_ty::PolyFnSig<'tcx>,
) -> Result<PolyFnSig, UnsupportedReason> {
    lower_binder(fn_sig, |fn_sig| {
        let inputs_and_output = List::from_vec(
            fn_sig
                .inputs_and_output
                .iter()
                .map(|ty| lower_ty(tcx, ty))
                .try_collect()?,
        );
        Ok(FnSig { inputs_and_output })
    })
}

fn lower_binder<S, T>(
    binder: rustc_ty::Binder<S>,
    mut f: impl FnMut(S) -> Result<T, UnsupportedReason>,
) -> Result<Binder<T>, UnsupportedReason> {
    let vars = lower_bound_vars(binder.bound_vars())?;
    Ok(Binder::bind_with_vars(f(binder.skip_binder())?, vars))
}

pub(crate) fn lower_bound_vars(
    bound_vars: &[rustc_ty::BoundVariableKind],
) -> Result<List<BoundVariableKind>, UnsupportedReason> {
    let mut vars = vec![];
    for var in bound_vars {
        match var {
            rustc_ty::BoundVariableKind::Region(kind) => {
                vars.push(BoundVariableKind::Region(*kind));
            }
            _ => {
                return Err(UnsupportedReason {
                    descr: format!("unsupported bound variable {var:?}"),
                });
            }
        }
    }
    Ok(List::from_vec(vars))
}

fn lower_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: rustc_ty::Const<'tcx>,
) -> Result<Const, UnsupportedReason> {
    let kind = match c.kind() {
        rustc_type_ir::ConstKind::Param(param_const) => {
            ConstKind::Param(ParamConst { name: param_const.name, index: param_const.index })
        }
        rustc_type_ir::ConstKind::Value(ty, ValTree::Leaf(scalar_int)) => {
            ConstKind::Value(lower_ty(tcx, ty)?, scalar_int)
        }
        _ => return Err(UnsupportedReason::new(format!("unsupported const {c:?}"))),
    };
    Ok(Const { kind })
}

pub(crate) fn lower_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_ty::Ty<'tcx>,
) -> Result<Ty, UnsupportedReason> {
    match ty.kind() {
        rustc_ty::Ref(region, ty, mutability) => {
            Ok(Ty::mk_ref(lower_region(region)?, lower_ty(tcx, *ty)?, *mutability))
        }
        rustc_ty::Bool => Ok(Ty::mk_bool()),
        rustc_ty::Int(int_ty) => Ok(Ty::mk_int(*int_ty)),
        rustc_ty::Uint(uint_ty) => Ok(Ty::mk_uint(*uint_ty)),
        rustc_ty::Float(float_ty) => Ok(Ty::mk_float(*float_ty)),
        rustc_ty::Param(param_ty) => Ok(Ty::mk_param(*param_ty)),
        rustc_ty::Adt(adt_def, args) => {
            let args = lower_generic_args(tcx, args)?;
            Ok(Ty::mk_adt(lower_adt_def(tcx, *adt_def), args))
        }
        rustc_ty::Never => Ok(Ty::mk_never()),
        rustc_ty::Str => Ok(Ty::mk_str()),
        rustc_ty::Char => Ok(Ty::mk_char()),
        rustc_ty::Tuple(tys) => {
            let tys = List::from_vec(tys.iter().map(|ty| lower_ty(tcx, ty)).try_collect()?);
            Ok(Ty::mk_tuple(tys))
        }
        rustc_ty::Array(ty, len) => Ok(Ty::mk_array(lower_ty(tcx, *ty)?, lower_const(tcx, *len)?)),
        rustc_ty::Slice(ty) => Ok(Ty::mk_slice(lower_ty(tcx, *ty)?)),
        rustc_ty::RawPtr(ty, mutbl) => {
            let ty = lower_ty(tcx, *ty)?;
            Ok(Ty::mk_raw_ptr(ty, *mutbl))
        }
        rustc_ty::FnPtr(fn_sig) => {
            let fn_sig = lower_fn_sig(tcx, *fn_sig)?;
            Ok(Ty::mk_fn_ptr(fn_sig))
        }
        rustc_ty::Closure(did, args) => {
            let args = lower_generic_args(tcx, args)?;
            Ok(Ty::mk_closure(*did, args))
        }

        rustc_ty::Alias(kind, alias_ty) => {
            let kind = lower_alias_kind(kind)?;
            let args = lower_generic_args(tcx, alias_ty.args)?;
            Ok(Ty::mk_alias(kind, alias_ty.def_id, args))
        }
        rustc_ty::Coroutine(did, args) => {
            let args = lower_generic_args(tcx, args)?;
            Ok(Ty::mk_coroutine(*did, args))
        }
        rustc_ty::CoroutineWitness(did, args) => {
            let args = lower_generic_args(tcx, args)?;
            Ok(Ty::mk_generator_witness(*did, args))
        }
        rustc_ty::Dynamic(predicates, region, rustc_ty::DynKind::Dyn) => {
            let region = lower_region(region)?;

            let exi_preds = List::from_vec(
                predicates
                    .iter()
                    .map(|pred| lower_existential_predicate(tcx, pred))
                    .try_collect()?,
            );

            Ok(Ty::mk_dynamic(exi_preds, region))
        }
        _ => Err(UnsupportedReason::new(format!("unsupported type `{ty:?}`"))),
    }
}

fn lower_alias_kind(kind: &rustc_ty::AliasTyKind) -> Result<AliasKind, UnsupportedReason> {
    match kind {
        rustc_type_ir::AliasTyKind::Projection => Ok(AliasKind::Projection),
        rustc_type_ir::AliasTyKind::Opaque => Ok(AliasKind::Opaque),
        _ => Err(UnsupportedReason::new(format!("unsupported alias kind `{kind:?}`"))),
    }
}

pub fn lower_adt_def<'tcx>(tcx: TyCtxt<'tcx>, adt_def: rustc_ty::AdtDef<'tcx>) -> AdtDef {
    AdtDef::new(AdtDefData::new(
        tcx,
        adt_def,
        adt_def.variants().iter().map(lower_variant).collect(),
    ))
}

fn lower_variant(variant: &rustc_ty::VariantDef) -> VariantDef {
    VariantDef {
        def_id: variant.def_id,
        name: variant.name,
        fields: variant.fields.iter().map(lower_field).collect(),
    }
}

fn lower_field(f: &rustc_ty::FieldDef) -> FieldDef {
    FieldDef { did: f.did, name: f.name }
}

pub fn lower_existential_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred: rustc_ty::Binder<rustc_ty::ExistentialPredicate<'tcx>>,
) -> Result<Binder<ExistentialPredicate>, UnsupportedReason> {
    assert!(pred.bound_vars().is_empty());
    let pred = pred.skip_binder();
    if let rustc_ty::ExistentialPredicate::Trait(exi_trait_ref) = pred {
        let def_id = exi_trait_ref.def_id;
        let args = lower_generic_args(tcx, exi_trait_ref.args)?;
        let exi_trait_ref = ExistentialTraitRef { def_id, args };
        Ok(Binder::bind_with_vars(ExistentialPredicate::Trait(exi_trait_ref), List::empty()))
    } else {
        Err(UnsupportedReason::new(format!("Unsupported existential predicate `{pred:?}`")))
    }
}

pub fn lower_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<List<GenericArg>, UnsupportedReason> {
    Ok(List::from_vec(
        args.iter()
            .map(|arg| lower_generic_arg(tcx, arg))
            .try_collect()?,
    ))
}

fn lower_generic_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    arg: rustc_middle::ty::GenericArg<'tcx>,
) -> Result<GenericArg, UnsupportedReason> {
    match arg.unpack() {
        GenericArgKind::Type(ty) => Ok(GenericArg::Ty(lower_ty(tcx, ty)?)),
        GenericArgKind::Lifetime(region) => Ok(GenericArg::Lifetime(lower_region(&region)?)),
        GenericArgKind::Const(c) => Ok(GenericArg::Const(lower_const(tcx, c)?)),
    }
}

fn lower_region(region: &rustc_middle::ty::Region) -> Result<Region, UnsupportedReason> {
    use rustc_middle::ty::RegionKind;
    match region.kind() {
        RegionKind::ReVar(rvid) => Ok(Region::ReVar(rvid)),
        RegionKind::ReBound(debruijn, bregion) => {
            Ok(Region::ReBound(debruijn, lower_bound_region(bregion)?))
        }
        RegionKind::ReEarlyParam(bregion) => Ok(Region::ReEarlyParam(bregion)),
        RegionKind::ReStatic => Ok(Region::ReStatic),
        RegionKind::ReLateParam(_)
        | RegionKind::RePlaceholder(_)
        | RegionKind::ReError(_)
        | RegionKind::ReErased => {
            Err(UnsupportedReason::new(format!("unsupported region `{region:?}`")))
        }
    }
}

fn lower_bound_region(
    bregion: rustc_middle::ty::BoundRegion,
) -> Result<BoundRegion, UnsupportedReason> {
    Ok(BoundRegion { kind: bregion.kind, var: bregion.var })
}

pub(crate) fn lower_generics(generics: &rustc_ty::Generics) -> Result<Generics, UnsupportedReason> {
    let params = List::from_vec(
        generics
            .own_params
            .iter()
            .map(lower_generic_param_def)
            .collect(),
    );
    Ok(Generics { params, orig: generics })
}

fn lower_generic_param_def(generic: &rustc_ty::GenericParamDef) -> GenericParamDef {
    let kind = match generic.kind {
        rustc_ty::GenericParamDefKind::Type { has_default, .. } => {
            GenericParamDefKind::Type { has_default }
        }
        rustc_ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
        rustc_ty::GenericParamDefKind::Const { has_default, is_host_effect, .. } => {
            GenericParamDefKind::Const { has_default, is_host_effect }
        }
    };
    GenericParamDef { def_id: generic.def_id, index: generic.index, name: generic.name, kind }
}

pub(crate) fn lower_generic_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: rustc_ty::GenericPredicates<'tcx>,
) -> Result<GenericPredicates, UnsupportedErr> {
    let predicates = generics
        .predicates
        .iter()
        .map(|(clause, span)| {
            lower_clause(tcx, clause).map_err(|reason| UnsupportedErr::new(reason).with_span(*span))
        })
        .try_collect()?;
    Ok(GenericPredicates { parent: generics.parent, predicates })
}

pub(crate) fn lower_item_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    bounds: &[rustc_ty::Clause<'tcx>],
) -> Result<List<Clause>, UnsupportedErr> {
    bounds
        .iter()
        .map(|clause| lower_clause(tcx, clause).map_err(UnsupportedErr::new))
        .try_collect()
}

fn lower_clause_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: &rustc_ty::ClauseKind<'tcx>,
) -> Result<ClauseKind, UnsupportedReason> {
    let kind = match kind {
        rustc_ty::ClauseKind::Trait(trait_pred) => {
            ClauseKind::Trait(TraitPredicate {
                trait_ref: lower_trait_ref(tcx, trait_pred.trait_ref)?,
            })
        }
        rustc_ty::ClauseKind::Projection(proj_pred) => {
            let Some(term) = proj_pred.term.as_type() else {
                return Err(UnsupportedReason::new(format!(
                    "unsupported projection predicate `{proj_pred:?}`"
                )));
            };
            let proj_ty = proj_pred.projection_term;
            let args = lower_generic_args(tcx, proj_ty.args)?;

            let projection_ty = AliasTy { args, def_id: proj_ty.def_id };
            let term = lower_ty(tcx, term)?;
            ClauseKind::Projection(ProjectionPredicate { projection_ty, term })
        }
        rustc_ty::ClauseKind::TypeOutlives(outlives_pred) => {
            ClauseKind::TypeOutlives(lower_type_outlives(tcx, *outlives_pred)?)
        }
        rustc_ty::ClauseKind::ConstArgHasType(const_, ty) => {
            ClauseKind::ConstArgHasType(lower_const(tcx, *const_)?, lower_ty(tcx, *ty)?)
        }
        _ => {
            return Err(UnsupportedReason::new(format!("unsupported clause kind `{kind:?}`")));
        }
    };
    Ok(kind)
}

fn lower_clause<'tcx>(
    tcx: TyCtxt<'tcx>,
    clause: &rustc_ty::Clause<'tcx>,
) -> Result<Clause, UnsupportedReason> {
    let kind = lower_binder(clause.kind(), |kind| lower_clause_kind(tcx, &kind))?;
    Ok(Clause::new(kind))
}

pub(crate) fn lower_trait_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: rustc_ty::TraitRef<'tcx>,
) -> Result<TraitRef, UnsupportedReason> {
    Ok(TraitRef { def_id: trait_ref.def_id, args: lower_generic_args(tcx, trait_ref.args)? })
}

fn lower_type_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    pred: rustc_ty::TypeOutlivesPredicate<'tcx>,
) -> Result<TypeOutlivesPredicate, UnsupportedReason> {
    Ok(OutlivesPredicate(lower_ty(tcx, pred.0)?, lower_region(&pred.1)?))
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_middle::mir as rustc_mir;
    use rustc_span::Span;

    use super::UnsupportedReason;

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_local_decl, code = E0999)]
    pub(super) struct UnsupportedLocalDecl<'tcx> {
        #[primary_span]
        #[label]
        span: Span,
        ty: rustc_middle::ty::Ty<'tcx>,
    }

    impl<'tcx> UnsupportedLocalDecl<'tcx> {
        pub(super) fn new(
            local_decl: &rustc_mir::LocalDecl<'tcx>,
            _err: UnsupportedReason,
        ) -> Self {
            Self { span: local_decl.source_info.span, ty: local_decl.ty }
        }
    }

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_mir, code = E0999)]
    #[note]
    pub(super) struct UnsupportedMir {
        #[primary_span]
        span: Span,
        kind: &'static str,
        reason: UnsupportedReason,
    }

    impl rustc_errors::IntoDiagArg for UnsupportedReason {
        fn into_diag_arg(self) -> rustc_errors::DiagArgValue {
            rustc_errors::DiagArgValue::Str(std::borrow::Cow::Owned(self.descr))
        }
    }

    impl UnsupportedMir {
        pub(super) fn new(span: Span, kind: &'static str, reason: UnsupportedReason) -> Self {
            Self { span, kind, reason }
        }

        pub(super) fn terminator(span: Span, reason: UnsupportedReason) -> Self {
            Self { span, kind: "terminator", reason }
        }

        pub(super) fn statement(span: Span, reason: UnsupportedReason) -> Self {
            Self { span, kind: "statement", reason }
        }
    }

    impl<'a, 'tcx> From<&'a rustc_mir::Terminator<'tcx>> for UnsupportedMir {
        fn from(terminator: &'a rustc_mir::Terminator<'tcx>) -> Self {
            Self::terminator(
                terminator.source_info.span,
                UnsupportedReason::new(format!("{terminator:?}",)),
            )
        }
    }

    impl<'a, 'tcx> From<&'a rustc_mir::Statement<'tcx>> for UnsupportedMir {
        fn from(statement: &'a rustc_mir::Statement<'tcx>) -> Self {
            Self::statement(
                statement.source_info.span,
                UnsupportedReason::new(format!("{statement:?}")),
            )
        }
    }
}
