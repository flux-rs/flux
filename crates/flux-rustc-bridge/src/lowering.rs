use flux_arc_interner::List;
use flux_common::result::ResultExt;
use flux_errors::FluxSession;
use itertools::Itertools;
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::{
    infer::{InferCtxt, TyCtxtInferExt},
    traits::Obligation,
};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::{
    mir::{self as rustc_mir, ConstValue},
    traits::{ImplSource, ObligationCause},
    ty::{
        self as rustc_ty, GenericArgKind, ParamConst, ParamEnv, TyCtxt, TypingMode,
        adjustment as rustc_adjustment,
    },
};
use rustc_span::{Span, Symbol};
use rustc_trait_selection::traits::SelectionContext;

use super::{
    mir::{
        AggregateKind, AssertKind, BasicBlockData, BinOp, Body, CallArgs, CastKind, Constant,
        LocalDecl, NonDivergingIntrinsic, NullOp, Operand, Place, PlaceElem, PointerCast, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AdtDef, AdtDefData, AliasKind, Binder, BoundRegion, BoundVariableKind, Clause, ClauseKind,
        Const, ConstKind, ExistentialPredicate, ExistentialProjection, FieldDef, FnSig, GenericArg,
        GenericParamDef, GenericParamDefKind, GenericPredicates, Generics, OutlivesPredicate,
        TraitPredicate, TraitRef, Ty, TypeOutlivesPredicate, UnevaluatedConst, VariantDef,
    },
};
use crate::{
    const_eval::{scalar_to_bits, scalar_to_int, scalar_to_uint},
    mir::{BodyRoot, CallKind},
    ty::{
        AliasTy, ExistentialTraitRef, GenericArgs, ProjectionPredicate, Region,
        RegionOutlivesPredicate,
    },
};

pub trait Lower<'tcx> {
    type R;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R;
}

pub struct MirLoweringCtxt<'a, 'sess, 'tcx> {
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
    pub span: Option<Span>,
}

impl UnsupportedErr {
    pub fn new(reason: UnsupportedReason) -> Self {
        UnsupportedErr { descr: reason.descr, span: None }
    }

    pub fn with_span(mut self, span: Span) -> Self {
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
    let trait_ref = tcx.erase_and_anonymize_regions(trait_ref);
    let obligation = Obligation::new(tcx, ObligationCause::dummy(), param_env, trait_ref);
    let impl_source = selcx.select(&obligation).ok()??;
    let impl_source = selcx.infcx.resolve_vars_if_possible(impl_source);
    // let impl_source = selcx.infcx.fully_resolve(impl_source).ok()?;
    let ImplSource::UserDefined(impl_data) = impl_source else { return None };
    Some((impl_data.impl_def_id, impl_data.args))
}

pub fn resolve_trait_ref_impl_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    trait_ref: rustc_ty::TraitRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let param_env = tcx.param_env(def_id);
    let infcx = tcx
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());
    trait_ref_impl_id(tcx, &mut SelectionContext::new(&infcx), param_env, trait_ref)
}

fn resolve_call_query<'tcx>(
    tcx: TyCtxt<'tcx>,
    selcx: &mut SelectionContext<'_, 'tcx>,
    param_env: ParamEnv<'tcx>,
    callee_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let trait_id = tcx.trait_of_assoc(callee_id)?;
    let trait_ref = rustc_ty::TraitRef::from_assoc(tcx, trait_id, args);
    let (impl_def_id, impl_args) = trait_ref_impl_id(tcx, selcx, param_env, trait_ref)?;
    let impl_args = args.rebase_onto(tcx, trait_id, impl_args);
    let assoc_id = tcx.impl_item_implementor_ids(impl_def_id).get(&callee_id)?;
    let assoc_item = tcx.associated_item(assoc_id);
    Some((assoc_item.def_id, impl_args))
}

impl<'sess, 'tcx> MirLoweringCtxt<'_, 'sess, 'tcx> {
    // We used to call `replicate_infer_ctxt` to compute the `infcx`
    // which replicated the [`InferCtxt`] used for mir typeck
    // by generating region variables for every region the body.
    // HOWEVER,the rustc folks hid access to the region-variables
    // so instead we have to take care to call `tcx.erase_regions(..)`
    // before using the `infcx` or `SelectionContext` to do any queries
    // (eg. see `get_impl_id_of_alias_reft` in projections.rs)
    pub fn lower_mir_body(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) -> Result<BodyRoot<'tcx>, ErrorGuaranteed> {
        let infcx = tcx
            .infer_ctxt()
            .with_next_trait_solver(true)
            .build(TypingMode::analysis_in_body(tcx, def_id));
        let rustc_body = body_with_facts.body;
        let def_id = rustc_body.source.def_id();

        let body = Self::lower_rustc_body(tcx, &infcx, sess, def_id, rustc_body)?;
        let promoted = body_with_facts
            .promoted
            .into_iter()
            .map(|rustc_promoted| Self::lower_rustc_body(tcx, &infcx, sess, def_id, rustc_promoted))
            .try_collect()?;

        let body_root = BodyRoot::new(
            body_with_facts.borrow_set,
            body_with_facts.region_inference_context,
            infcx,
            body,
            promoted,
        );
        Ok(body_root)
    }

    fn lower_rustc_body(
        tcx: TyCtxt<'tcx>,
        infcx: &InferCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: DefId,
        body: rustc_mir::Body<'tcx>,
    ) -> Result<Body<'tcx>, ErrorGuaranteed> {
        let selcx = SelectionContext::new(infcx);
        let param_env = tcx.param_env(def_id);
        let mut lower = MirLoweringCtxt { tcx, selcx, param_env, sess, rustc_mir: &body };

        let basic_blocks = body
            .basic_blocks
            .iter()
            .map(|bb_data| lower.lower_basic_block_data(bb_data))
            .try_collect()?;

        let local_decls = body
            .local_decls
            .iter()
            .map(|local_decl| lower.lower_local_decl(local_decl))
            .try_collect()?;

        Ok(Body::new(basic_blocks, local_decls, body))
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
            ty: local_decl
                .ty
                .lower(self.tcx)
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
                    lower_place(self.tcx, place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    self.lower_rvalue(rvalue)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )
            }
            rustc_mir::StatementKind::SetDiscriminant { place, variant_index } => {
                StatementKind::SetDiscriminant(
                    lower_place(self.tcx, place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    *variant_index,
                )
            }
            rustc_mir::StatementKind::FakeRead(box (cause, place)) => {
                StatementKind::FakeRead(Box::new((
                    *cause,
                    lower_place(self.tcx, place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )))
            }
            rustc_mir::StatementKind::PlaceMention(place) => {
                StatementKind::PlaceMention(
                    lower_place(self.tcx, place)
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
                    lower_place(self.tcx, place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    *variance,
                )
            }
            rustc_mir::StatementKind::Intrinsic(ndi) => {
                match ndi.as_ref() {
                    rustc_mir::NonDivergingIntrinsic::Assume(op) => {
                        let op = self
                            .lower_operand(op)
                            .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                            .emit(self.sess)?;
                        StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))
                    }
                    rustc_mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                        return Err(errors::UnsupportedMir::from(stmt)).emit(self.sess);
                    }
                }
            }

            rustc_mir::StatementKind::Retag(_, _)
            | rustc_mir::StatementKind::Deinit(_)
            | rustc_mir::StatementKind::AscribeUserType(..)
            | rustc_mir::StatementKind::Coverage(_)
            | rustc_mir::StatementKind::ConstEvalCounter
            | rustc_mir::StatementKind::BackwardIncompatibleDropHint { .. } => {
                return Err(errors::UnsupportedMir::from(stmt)).emit(self.sess);
            }
        };
        Ok(Statement { kind, source_info: stmt.source_info })
    }

    fn lower_terminator(
        &mut self,
        terminator: &rustc_mir::Terminator<'tcx>,
    ) -> Result<Terminator<'tcx>, ErrorGuaranteed> {
        let span = terminator.source_info.span;
        let kind = match &terminator.kind {
            rustc_mir::TerminatorKind::Return => TerminatorKind::Return,
            rustc_mir::TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
                let kind = {
                    let func_ty = func.ty(self.rustc_mir, self.tcx);
                    match func_ty.kind() {
                        rustc_middle::ty::TyKind::FnDef(fn_def, args) => {
                            let lowered = args
                                .lower(self.tcx)
                                .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                                .emit(self.sess)?;
                            let def_id = *fn_def;
                            let generic_args = CallArgs { orig: args, lowered };
                            let (resolved_id, resolved_args) = self
                                .resolve_call(def_id, generic_args.orig)
                                .map_err(|reason| {
                                    errors::UnsupportedMir::new(span, "terminator call", reason)
                                })
                                .emit(self.sess)?;
                            CallKind::FnDef { def_id, generic_args, resolved_id, resolved_args }
                        }
                        rustc_middle::ty::TyKind::FnPtr(fn_sig_tys, header) => {
                            let fn_sig = fnptr_as_fnsig(fn_sig_tys, header)
                                .lower(self.tcx)
                                .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                                .emit(self.sess)?;
                            let operand = self
                                .lower_operand(func)
                                .map_err(|reason| {
                                    errors::UnsupportedMir::new(
                                        span,
                                        "function pointer target",
                                        reason,
                                    )
                                })
                                .emit(self.sess)?;
                            CallKind::FnPtr { fn_sig, operand }
                        }
                        _ => {
                            Err(errors::UnsupportedMir::terminator(
                                span,
                                UnsupportedReason::new(format!(
                                    "unsupported callee type `{func_ty:?}`"
                                )),
                            ))
                            .emit(self.sess)?
                        }
                    }
                };

                let destination = lower_place(self.tcx, destination)
                    .map_err(|reason| {
                        errors::UnsupportedMir::new(span, "terminator destination", reason)
                    })
                    .emit(self.sess)?;

                TerminatorKind::Call {
                    kind,
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
                    place: lower_place(self.tcx, place)
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
                    resume_arg: lower_place(self.tcx, resume_arg)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    drop: *drop,
                }
            }
            rustc_mir::TerminatorKind::CoroutineDrop => TerminatorKind::CoroutineDrop,
            rustc_mir::TerminatorKind::UnwindResume => TerminatorKind::UnwindResume,
            rustc_mir::TerminatorKind::UnwindTerminate(..)
            | rustc_mir::TerminatorKind::TailCall { .. }
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
        let call_args = CallArgs { lowered: resolved_args.lower(self.tcx)?, orig: resolved_args };
        Ok((resolved_id, call_args))
    }

    fn lower_rvalue(&self, rvalue: &rustc_mir::Rvalue<'tcx>) -> Result<Rvalue, UnsupportedReason> {
        match rvalue {
            rustc_mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            rustc_mir::Rvalue::Repeat(op, c) => {
                let op = self.lower_operand(op)?;
                let c = c.lower(self.tcx)?;
                Ok(Rvalue::Repeat(op, c))
            }
            rustc_mir::Rvalue::Ref(region, bk, p) => {
                Ok(Rvalue::Ref(region.lower(self.tcx)?, *bk, lower_place(self.tcx, p)?))
            }
            rustc_mir::Rvalue::RawPtr(kind, place) => {
                Ok(Rvalue::RawPtr(*kind, lower_place(self.tcx, place)?))
            }
            rustc_mir::Rvalue::Cast(kind, op, ty) => {
                let kind = self.lower_cast_kind(*kind).ok_or_else(|| {
                    UnsupportedReason::new(format!("unsupported cast `{kind:?}`"))
                })?;
                let op = self.lower_operand(op)?;
                let ty = ty.lower(self.tcx)?;
                Ok(Rvalue::Cast(kind, op, ty))
            }
            rustc_mir::Rvalue::BinaryOp(bin_op, box (op1, op2)) => {
                Ok(Rvalue::BinaryOp(
                    self.lower_bin_op(*bin_op)?,
                    self.lower_operand(op1)?,
                    self.lower_operand(op2)?,
                ))
            }
            rustc_mir::Rvalue::NullaryOp(null_op, ty) => {
                Ok(Rvalue::NullaryOp(self.lower_null_op(*null_op)?, ty.lower(self.tcx)?))
            }
            rustc_mir::Rvalue::UnaryOp(un_op, op) => {
                Ok(Rvalue::UnaryOp(*un_op, self.lower_operand(op)?))
            }
            rustc_mir::Rvalue::Discriminant(p) => {
                Ok(Rvalue::Discriminant(lower_place(self.tcx, p)?))
            }
            rustc_mir::Rvalue::Aggregate(aggregate_kind, args) => {
                let aggregate_kind = self.lower_aggregate_kind(aggregate_kind)?;
                let args = args.iter().map(|op| self.lower_operand(op)).try_collect()?;
                Ok(Rvalue::Aggregate(aggregate_kind, args))
            }
            rustc_mir::Rvalue::ShallowInitBox(op, ty) => {
                Ok(Rvalue::ShallowInitBox(self.lower_operand(op)?, ty.lower(self.tcx)?))
            }
            rustc_mir::Rvalue::ThreadLocalRef(_)
            | rustc_mir::Rvalue::CopyForDeref(_)
            | rustc_mir::Rvalue::WrapUnsafeBinder(..) => {
                Err(UnsupportedReason::new(format!("unsupported rvalue `{rvalue:?}`")))
            }
        }
    }

    fn lower_pointer_coercion(
        &self,
        coercion: rustc_adjustment::PointerCoercion,
    ) -> Option<PointerCast> {
        match coercion {
            rustc_adjustment::PointerCoercion::MutToConstPointer => {
                Some(crate::mir::PointerCast::MutToConstPointer)
            }
            rustc_adjustment::PointerCoercion::Unsize => Some(crate::mir::PointerCast::Unsize),
            rustc_adjustment::PointerCoercion::ClosureFnPointer(_) => {
                Some(crate::mir::PointerCast::ClosureFnPointer)
            }
            rustc_adjustment::PointerCoercion::ReifyFnPointer => {
                Some(crate::mir::PointerCast::ReifyFnPointer)
            }
            rustc_adjustment::PointerCoercion::UnsafeFnPointer
            | rustc_adjustment::PointerCoercion::ArrayToPointer => None,
        }
    }
    fn lower_cast_kind(&self, kind: rustc_mir::CastKind) -> Option<CastKind> {
        match kind {
            rustc_mir::CastKind::IntToInt => Some(CastKind::IntToInt),
            rustc_mir::CastKind::IntToFloat => Some(CastKind::IntToFloat),
            rustc_mir::CastKind::FloatToInt => Some(CastKind::FloatToInt),
            rustc_mir::CastKind::PtrToPtr => Some(CastKind::PtrToPtr),
            rustc_mir::CastKind::PointerCoercion(ptr_coercion, _) => {
                Some(CastKind::PointerCoercion(self.lower_pointer_coercion(ptr_coercion)?))
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
            rustc_mir::AggregateKind::Adt(
                def_id,
                variant_idx,
                args,
                user_type_annot_idx,
                field_idx,
            ) => {
                Ok(AggregateKind::Adt(
                    *def_id,
                    *variant_idx,
                    args.lower(self.tcx)?,
                    *user_type_annot_idx,
                    *field_idx,
                ))
            }
            rustc_mir::AggregateKind::Array(ty) => Ok(AggregateKind::Array(ty.lower(self.tcx)?)),
            rustc_mir::AggregateKind::Tuple => Ok(AggregateKind::Tuple),
            rustc_mir::AggregateKind::Closure(did, args) => {
                let args = args.lower(self.tcx)?;
                Ok(AggregateKind::Closure(*did, args))
            }
            rustc_mir::AggregateKind::Coroutine(did, args) => {
                let args = args.lower(self.tcx)?;
                Ok(AggregateKind::Coroutine(*did, args))
            }
            rustc_mir::AggregateKind::RawPtr(_, _)
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

    fn lower_null_op(&self, null_op: rustc_mir::NullOp) -> Result<NullOp, UnsupportedReason> {
        match null_op {
            rustc_mir::NullOp::SizeOf => Ok(NullOp::SizeOf),
            rustc_mir::NullOp::AlignOf => Ok(NullOp::AlignOf),
            rustc_mir::NullOp::OffsetOf(_)
            | rustc_mir::NullOp::UbChecks
            | rustc_mir::NullOp::ContractChecks => {
                Err(UnsupportedReason::new(format!("unsupported nullary op `{null_op:?}`")))
            }
        }
    }

    fn lower_operand(&self, op: &rustc_mir::Operand<'tcx>) -> Result<Operand, UnsupportedReason> {
        match op {
            rustc_mir::Operand::Copy(place) => Ok(Operand::Copy(lower_place(self.tcx, place)?)),
            rustc_mir::Operand::Move(place) => Ok(Operand::Move(lower_place(self.tcx, place)?)),
            rustc_mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
        }
    }

    fn lower_constant(
        &self,
        constant: &rustc_mir::ConstOperand<'tcx>,
    ) -> Result<Constant, UnsupportedReason> {
        use rustc_middle::ty::TyKind;
        use rustc_mir::{Const, interpret::Scalar};
        let tcx = self.tcx;
        let const_ = constant.const_;
        let ty = constant.ty();
        match (constant.const_, ty.kind()) {
            (Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), ty), _) => {
                self.scalar_int_to_constant(scalar, ty)
            }
            (Const::Val(ct @ ConstValue::Slice { .. }, _), TyKind::Ref(_, ref_ty, _))
                if ref_ty.is_str() =>
            {
                if let Some(data) = ct.try_get_slice_bytes_for_diagnostics(tcx) {
                    let str = String::from_utf8_lossy(data);
                    Some(Constant::Str(Symbol::intern(&str)))
                } else {
                    None
                }
            }
            (Const::Ty(ty, c), _) => {
                match c.kind() {
                    rustc_ty::ConstKind::Value(value) => {
                        match &*value.valtree {
                            rustc_ty::ValTreeKind::Leaf(scalar_int) => {
                                self.scalar_int_to_constant(*scalar_int, value.ty)
                            }
                            rustc_ty::ValTreeKind::Branch(_) => None,
                        }
                    }
                    rustc_ty::ConstKind::Param(param_const) => {
                        let ty = ty.lower(tcx)?;
                        Some(Constant::Param(param_const, ty))
                    }
                    _ => None,
                }
            }
            (_, TyKind::Tuple(tys)) if tys.is_empty() => return Ok(Constant::Unit),

            (_, _) => {
                if let Const::Unevaluated(uneval, _) = const_ {
                    let args = uneval.args.lower(tcx)?;
                    if args.is_empty() {
                        let ty = ty.lower(tcx)?;
                        let uneval =
                            UnevaluatedConst { def: uneval.def, args, promoted: uneval.promoted };
                        return Ok(Constant::Unevaluated(ty, uneval));
                    }
                    // HACK(RJ) see tests/tests/pos/surface/const09.rs
                    // The const has `args` which makes it unevaluated...
                    let typing_env = self.selcx.infcx.typing_env(self.param_env);
                    let const_ = constant
                        .const_
                        .eval(tcx, typing_env, rustc_span::DUMMY_SP)
                        .map(|val| Const::Val(val, constant.const_.ty()))
                        .unwrap_or(constant.const_);
                    if let Const::Val(ConstValue::Scalar(Scalar::Int(scalar)), ty) = const_
                        && let Some(constant) = self.scalar_int_to_constant(scalar, ty)
                    {
                        return Ok(constant);
                    }
                }
                Some(Constant::Opaque(ty.lower(tcx)?))
            }
        }
        .ok_or_else(|| UnsupportedReason::new(format!("unsupported constant `{constant:?}`")))
    }

    /// A `ScalarInt` is just a set of bits that can represent any scalar value.
    /// This can represent all the primitive types with a fixed size.
    fn scalar_int_to_constant(
        &self,
        scalar: rustc_ty::ScalarInt,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) -> Option<Constant> {
        use rustc_middle::ty::TyKind;
        let kind = ty.kind();
        match kind {
            TyKind::Int(int_ty) => {
                Some(Constant::Int(scalar_to_int(self.tcx, scalar, *int_ty), *int_ty))
            }
            TyKind::Uint(uint_ty) => {
                Some(Constant::Uint(scalar_to_uint(self.tcx, scalar, *uint_ty), *uint_ty))
            }
            TyKind::Float(float_ty) => {
                Some(Constant::Float(scalar_to_bits(self.tcx, scalar, ty).unwrap(), *float_ty))
            }
            TyKind::Char => Some(Constant::Char(scalar.try_into().unwrap())),
            TyKind::Bool => Some(Constant::Bool(scalar.try_to_bool().unwrap())),
            TyKind::Tuple(tys) if tys.is_empty() => Some(Constant::Unit),
            _ => {
                match ty.lower(self.tcx) {
                    Ok(ty) => Some(Constant::Opaque(ty)),
                    Err(_) => None,
                }
            }
        }
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

pub fn lower_place<'tcx>(
    _tcx: TyCtxt<'tcx>,
    place: &rustc_mir::Place<'tcx>,
) -> Result<Place, UnsupportedReason> {
    let mut projection = vec![];
    for elem in place.projection {
        match elem {
            rustc_mir::PlaceElem::Deref => projection.push(PlaceElem::Deref),
            rustc_mir::PlaceElem::Field(field, _) => projection.push(PlaceElem::Field(field)),
            rustc_mir::PlaceElem::Downcast(name, idx) => {
                projection.push(PlaceElem::Downcast(name, idx));
            }
            rustc_mir::PlaceElem::Index(v) => projection.push(PlaceElem::Index(v)),
            rustc_mir::ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                projection.push(PlaceElem::ConstantIndex { offset, min_length, from_end });
            }
            _ => {
                return Err(UnsupportedReason::new(format!("unsupported place `{place:?}`")));
            }
        }
    }
    Ok(Place { local: place.local, projection })
}

impl<'tcx> Lower<'tcx> for rustc_ty::FnSig<'tcx> {
    type R = Result<FnSig, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let inputs_and_output = List::from_vec(
            self.inputs_and_output
                .iter()
                .map(|ty| ty.lower(tcx))
                .try_collect()?,
        );
        Ok(FnSig { safety: self.safety, abi: self.abi, inputs_and_output })
    }
}

impl<'tcx> Lower<'tcx> for &'tcx rustc_ty::List<rustc_ty::BoundVariableKind> {
    type R = Result<List<BoundVariableKind>, UnsupportedReason>;

    fn lower(self, _tcx: TyCtxt<'tcx>) -> Self::R {
        let mut vars = vec![];
        for var in self {
            match var {
                rustc_ty::BoundVariableKind::Region(kind) => {
                    vars.push(BoundVariableKind::Region(kind));
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
}

impl<'tcx> Lower<'tcx> for rustc_ty::ValTree<'tcx> {
    type R = crate::ty::ValTree;

    fn lower(self, _tcx: TyCtxt<'tcx>) -> Self::R {
        match &*self {
            rustc_ty::ValTreeKind::Leaf(scalar_int) => crate::ty::ValTree::Leaf(*scalar_int),
            rustc_ty::ValTreeKind::Branch(trees) => {
                let trees = trees.iter().map(|tree| tree.lower(_tcx)).collect();
                crate::ty::ValTree::Branch(trees)
            }
        }
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::Const<'tcx> {
    type R = Result<Const, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let kind = match self.kind() {
            rustc_type_ir::ConstKind::Param(param_const) => {
                ConstKind::Param(ParamConst { name: param_const.name, index: param_const.index })
            }
            rustc_type_ir::ConstKind::Value(value) => {
                ConstKind::Value(value.ty.lower(tcx)?, value.valtree.lower(tcx))
            }
            rustc_type_ir::ConstKind::Unevaluated(c) => {
                // TODO: raise unsupported if c.args is not empty?
                let args = c.args.lower(tcx)?;
                ConstKind::Unevaluated(UnevaluatedConst { def: c.def, args, promoted: None })
            }
            _ => return Err(UnsupportedReason::new(format!("unsupported const {self:?}"))),
        };
        Ok(Const { kind })
    }
}

impl<'tcx, T, S> Lower<'tcx> for rustc_ty::Binder<'tcx, T>
where
    T: Lower<'tcx, R = Result<S, UnsupportedReason>>,
{
    type R = Result<Binder<S>, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let vars = self.bound_vars().lower(tcx)?;
        Ok(Binder::bind_with_vars(self.skip_binder().lower(tcx)?, vars))
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::Ty<'tcx> {
    type R = Result<Ty, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        match self.kind() {
            rustc_ty::Ref(region, ty, mutability) => {
                Ok(Ty::mk_ref(region.lower(tcx)?, ty.lower(tcx)?, *mutability))
            }
            rustc_ty::Bool => Ok(Ty::mk_bool()),
            rustc_ty::Int(int_ty) => Ok(Ty::mk_int(*int_ty)),
            rustc_ty::Uint(uint_ty) => Ok(Ty::mk_uint(*uint_ty)),
            rustc_ty::Float(float_ty) => Ok(Ty::mk_float(*float_ty)),
            rustc_ty::Param(param_ty) => Ok(Ty::mk_param(*param_ty)),
            rustc_ty::Adt(adt_def, args) => {
                let args = args.lower(tcx)?;
                Ok(Ty::mk_adt(adt_def.lower(tcx), args))
            }
            rustc_ty::FnDef(def_id, args) => {
                let args = args.lower(tcx)?;
                Ok(Ty::mk_fn_def(*def_id, args))
            }
            rustc_ty::Never => Ok(Ty::mk_never()),
            rustc_ty::Str => Ok(Ty::mk_str()),
            rustc_ty::Char => Ok(Ty::mk_char()),
            rustc_ty::Tuple(tys) => {
                let tys = List::from_vec(tys.iter().map(|ty| ty.lower(tcx)).try_collect()?);
                Ok(Ty::mk_tuple(tys))
            }
            rustc_ty::Array(ty, len) => Ok(Ty::mk_array(ty.lower(tcx)?, len.lower(tcx)?)),
            rustc_ty::Slice(ty) => Ok(Ty::mk_slice(ty.lower(tcx)?)),
            rustc_ty::RawPtr(ty, mutbl) => {
                let ty = ty.lower(tcx)?;
                Ok(Ty::mk_raw_ptr(ty, *mutbl))
            }
            rustc_ty::FnPtr(fn_sig_tys, header) => {
                let fn_sig = fnptr_as_fnsig(fn_sig_tys, header).lower(tcx)?;
                Ok(Ty::mk_fn_ptr(fn_sig))
            }
            rustc_ty::Closure(did, args) => {
                let args = args.lower(tcx)?;
                Ok(Ty::mk_closure(*did, args))
            }

            rustc_ty::Alias(kind, alias_ty) => {
                let kind = kind.lower(tcx)?;
                let args = alias_ty.args.lower(tcx)?;
                Ok(Ty::mk_alias(kind, alias_ty.def_id, args))
            }
            rustc_ty::Coroutine(did, args) => {
                let args = args.lower(tcx)?;
                Ok(Ty::mk_coroutine(*did, args))
            }
            rustc_ty::CoroutineWitness(did, args) => {
                let args = args.lower(tcx)?;
                Ok(Ty::mk_generator_witness(*did, args))
            }
            rustc_ty::Dynamic(predicates, region) => {
                let region = region.lower(tcx)?;

                let exi_preds = List::from_vec(
                    predicates
                        .iter()
                        .map(|pred| pred.lower(tcx))
                        .try_collect()?,
                );

                Ok(Ty::mk_dynamic(exi_preds, region))
            }
            rustc_ty::Foreign(def_id) => Ok(Ty::mk_foreign(*def_id)),
            _ => Err(UnsupportedReason::new(format!("unsupported type `{self:?}`"))),
        }
    }
}

fn fnptr_as_fnsig<'tcx>(
    fn_sig_tys: &'tcx rustc_ty::Binder<'tcx, rustc_ty::FnSigTys<TyCtxt<'tcx>>>,
    header: &'tcx rustc_ty::FnHeader<TyCtxt<'tcx>>,
) -> rustc_ty::Binder<'tcx, rustc_ty::FnSig<'tcx>> {
    fn_sig_tys.map_bound(|fn_sig_tys| {
        rustc_ty::FnSig {
            inputs_and_output: fn_sig_tys.inputs_and_output,
            c_variadic: header.c_variadic,
            safety: header.safety,
            abi: header.abi,
        }
    })
}

impl<'tcx> Lower<'tcx> for rustc_ty::AliasTyKind {
    type R = Result<AliasKind, UnsupportedReason>;

    fn lower(self, _tcx: TyCtxt<'tcx>) -> Self::R {
        match self {
            rustc_type_ir::AliasTyKind::Projection => Ok(AliasKind::Projection),
            rustc_type_ir::AliasTyKind::Opaque => Ok(AliasKind::Opaque),
            _ => Err(UnsupportedReason::new(format!("unsupported alias kind `{self:?}`"))),
        }
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::AdtDef<'tcx> {
    type R = AdtDef;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        AdtDef::new(AdtDefData::new(
            tcx,
            self,
            self.variants()
                .iter()
                .map(|variant| {
                    VariantDef {
                        def_id: variant.def_id,
                        name: variant.name,
                        fields: variant
                            .fields
                            .iter()
                            .map(|f| FieldDef { did: f.did, name: f.name })
                            .collect(),
                    }
                })
                .collect(),
        ))
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::ExistentialPredicate<'tcx> {
    type R = Result<ExistentialPredicate, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        match self {
            rustc_type_ir::ExistentialPredicate::Trait(trait_ref) => {
                Ok(ExistentialPredicate::Trait(ExistentialTraitRef {
                    def_id: trait_ref.def_id,
                    args: trait_ref.args.lower(tcx)?,
                }))
            }
            rustc_type_ir::ExistentialPredicate::Projection(proj) => {
                let Some(term) = proj.term.as_type() else {
                    return Err(UnsupportedReason::new(format!(
                        "unsupported existential predicate `{self:?}`"
                    )));
                };
                Ok(ExistentialPredicate::Projection(ExistentialProjection {
                    def_id: proj.def_id,
                    args: proj.args.lower(tcx)?,
                    term: term.lower(tcx)?,
                }))
            }
            rustc_type_ir::ExistentialPredicate::AutoTrait(def_id) => {
                Ok(ExistentialPredicate::AutoTrait(def_id))
            }
        }
    }
}

impl<'tcx> Lower<'tcx> for rustc_middle::ty::GenericArgsRef<'tcx> {
    type R = Result<GenericArgs, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        Ok(List::from_vec(self.iter().map(|arg| arg.lower(tcx)).try_collect()?))
    }
}

impl<'tcx> Lower<'tcx> for rustc_middle::ty::GenericArg<'tcx> {
    type R = Result<GenericArg, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        match self.kind() {
            GenericArgKind::Type(ty) => Ok(GenericArg::Ty(ty.lower(tcx)?)),
            GenericArgKind::Lifetime(region) => Ok(GenericArg::Lifetime(region.lower(tcx)?)),
            GenericArgKind::Const(c) => Ok(GenericArg::Const(c.lower(tcx)?)),
        }
    }
}

impl<'tcx> Lower<'tcx> for rustc_middle::ty::Region<'tcx> {
    type R = Result<Region, UnsupportedReason>;

    fn lower(self, _tcx: TyCtxt<'tcx>) -> Self::R {
        use rustc_middle::ty;
        match self.kind() {
            ty::ReVar(rvid) => Ok(Region::ReVar(rvid)),
            ty::ReBound(ty::BoundVarIndexKind::Bound(debruijn), bregion) => {
                Ok(Region::ReBound(
                    debruijn,
                    Ok(BoundRegion { kind: bregion.kind, var: bregion.var })?,
                ))
            }
            ty::ReEarlyParam(bregion) => Ok(Region::ReEarlyParam(bregion)),
            ty::ReStatic => Ok(Region::ReStatic),
            ty::ReErased => Ok(Region::ReErased),
            ty::ReBound(ty::BoundVarIndexKind::Canonical, _)
            | ty::ReLateParam(_)
            | ty::RePlaceholder(_)
            | ty::ReError(_) => {
                Err(UnsupportedReason::new(format!("unsupported region `{self:?}`")))
            }
        }
    }
}

impl<'tcx> Lower<'tcx> for &'tcx rustc_middle::ty::Generics {
    type R = Generics<'tcx>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let params = List::from_vec(
            self.own_params
                .iter()
                .map(|param| param.lower(tcx))
                .collect(),
        );
        Generics { params, orig: self }
    }
}

impl<'tcx> Lower<'tcx> for &rustc_middle::ty::GenericParamDef {
    type R = GenericParamDef;

    fn lower(self, _tcx: TyCtxt<'tcx>) -> Self::R {
        let kind = match self.kind {
            rustc_ty::GenericParamDefKind::Type { has_default, .. } => {
                GenericParamDefKind::Type { has_default }
            }
            rustc_ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
            rustc_ty::GenericParamDefKind::Const { has_default, .. } => {
                GenericParamDefKind::Const { has_default }
            }
        };
        GenericParamDef { def_id: self.def_id, index: self.index, name: self.name, kind }
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::GenericPredicates<'tcx> {
    type R = Result<GenericPredicates, UnsupportedErr>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let predicates = self
            .predicates
            .iter()
            .map(|(clause, span)| {
                clause
                    .lower(tcx)
                    .map_err(|reason| UnsupportedErr::new(reason).with_span(*span))
            })
            .try_collect()?;
        Ok(GenericPredicates { parent: self.parent, predicates })
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::Clauses<'tcx> {
    type R = Result<List<Clause>, UnsupportedErr>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        self.iter()
            .map(|clause| clause.lower(tcx).map_err(UnsupportedErr::new))
            .try_collect()
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::ClauseKind<'tcx> {
    type R = Result<ClauseKind, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        let kind = match self {
            rustc_ty::ClauseKind::Trait(trait_pred) => {
                ClauseKind::Trait(TraitPredicate { trait_ref: trait_pred.trait_ref.lower(tcx)? })
            }
            rustc_ty::ClauseKind::Projection(proj_pred) => {
                let Some(term) = proj_pred.term.as_type() else {
                    return Err(UnsupportedReason::new(format!(
                        "unsupported projection predicate `{proj_pred:?}`"
                    )));
                };
                let proj_ty = proj_pred.projection_term;
                let args = proj_ty.args.lower(tcx)?;

                let projection_ty = AliasTy { args, def_id: proj_ty.def_id };
                let term = term.lower(tcx)?;
                ClauseKind::Projection(ProjectionPredicate { projection_ty, term })
            }
            rustc_ty::ClauseKind::RegionOutlives(outlives) => {
                ClauseKind::RegionOutlives(outlives.lower(tcx)?)
            }
            rustc_ty::ClauseKind::TypeOutlives(outlives) => {
                ClauseKind::TypeOutlives(outlives.lower(tcx)?)
            }
            rustc_ty::ClauseKind::ConstArgHasType(const_, ty) => {
                ClauseKind::ConstArgHasType(const_.lower(tcx)?, ty.lower(tcx)?)
            }
            _ => {
                return Err(UnsupportedReason::new(format!("unsupported clause kind `{self:?}`")));
            }
        };
        Ok(kind)
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::Clause<'tcx> {
    type R = Result<Clause, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        Ok(Clause::new(self.kind().lower(tcx)?))
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::TraitRef<'tcx> {
    type R = Result<TraitRef, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        Ok(TraitRef { def_id: self.def_id, args: self.args.lower(tcx)? })
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::TypeOutlivesPredicate<'tcx> {
    type R = Result<TypeOutlivesPredicate, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        Ok(OutlivesPredicate(self.0.lower(tcx)?, self.1.lower(tcx)?))
    }
}

impl<'tcx> Lower<'tcx> for rustc_ty::RegionOutlivesPredicate<'tcx> {
    type R = Result<RegionOutlivesPredicate, UnsupportedReason>;

    fn lower(self, tcx: TyCtxt<'tcx>) -> Self::R {
        Ok(OutlivesPredicate(self.0.lower(tcx)?, self.1.lower(tcx)?))
    }
}

mod errors {
    use std::path::PathBuf;

    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_middle::mir as rustc_mir;
    use rustc_span::Span;

    use super::UnsupportedReason;

    #[derive(Diagnostic)]
    #[diag(rustc_bridge_unsupported_local_decl, code = E0999)]
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
    #[diag(rustc_bridge_unsupported_mir, code = E0999)]
    #[note]
    pub(super) struct UnsupportedMir {
        #[primary_span]
        span: Span,
        kind: &'static str,
        reason: UnsupportedReason,
    }

    impl rustc_errors::IntoDiagArg for UnsupportedReason {
        fn into_diag_arg(self, _path: &mut Option<PathBuf>) -> rustc_errors::DiagArgValue {
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
