use std::collections::hash_map;

use flux_common::index::IndexVec;
use flux_errors::{FluxSession, ResultExt};
use itertools::Itertools;
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_const_eval::interpret::ConstValue;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir as rustc_mir,
    ty::{self as rustc_ty, adjustment as rustc_adjustment, GenericArgKind, ParamEnv, TyCtxt},
};

use super::{
    mir::{
        AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp, Body, BorrowKind, CallSubsts,
        CastKind, Constant, FakeReadCause, LocalDecl, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AdtDef, AdtDefData, AliasKind, Binder, BoundRegion, BoundRegionKind, BoundVariableKind,
        Clause, ClauseKind, Const, FieldDef, FnSig, GenericArg, GenericParamDef,
        GenericParamDefKind, GenericPredicates, Generics, PolyFnSig, Ty, VariantDef,
    },
};
use crate::{
    const_eval::scalar_int_to_constant,
    intern::List,
    rustc::ty::{AliasTy, ProjectionPredicate, Region, RegionVar},
};

pub struct LoweringCtxt<'a, 'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'sess FluxSession,
    rustc_mir: &'a rustc_mir::Body<'tcx>,
}

#[derive(Debug, Clone)]
pub struct UnsupportedReason {
    pub(crate) descr: String,
}

impl<'sess, 'tcx> LoweringCtxt<'_, 'sess, 'tcx> {
    pub fn lower_mir_body(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) -> Result<Body<'tcx>, ErrorGuaranteed> {
        let lower = LoweringCtxt { tcx, sess, rustc_mir: &body_with_facts.body };

        let basic_blocks = lower
            .rustc_mir
            .basic_blocks
            .iter()
            .map(|bb_data| lower.lower_basic_block_data(bb_data))
            .try_collect()?;

        let fake_predecessors = mk_fake_predecessors(&basic_blocks);

        let local_decls = lower
            .rustc_mir
            .local_decls
            .iter()
            .map(|local_decl| lower.lower_local_decl(local_decl))
            .try_collect()?;

        Ok(Body { basic_blocks, local_decls, fake_predecessors, body_with_facts })
    }

    fn lower_basic_block_data(
        &self,
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
        &self,
        terminator: &rustc_mir::Terminator<'tcx>,
    ) -> Result<Terminator<'tcx>, ErrorGuaranteed> {
        let span = terminator.source_info.span;
        let kind = match &terminator.kind {
            rustc_mir::TerminatorKind::Return => TerminatorKind::Return,
            rustc_mir::TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
                let (func, substs) = match func.ty(self.rustc_mir, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, substs) => {
                        let lowered_substs = lower_generic_args(self.tcx, substs)
                            .map_err(|_err| errors::UnsupportedMir::from(terminator))
                            .emit(self.sess)?;
                        (*fn_def, CallSubsts { orig: substs, lowered: lowered_substs })
                    }
                    _ => Err(errors::UnsupportedMir::from(terminator)).emit(self.sess)?,
                };

                let destination = lower_place(destination)
                    .map_err(|reason| {
                        errors::UnsupportedMir::new(span, "terminator destination", reason)
                    })
                    .emit(self.sess)?;

                let resolved_call = self
                    .resolve_call(func, substs.orig)
                    .map_err(|reason| errors::UnsupportedMir::new(span, "terminator call", reason))
                    .emit(self.sess)?;

                TerminatorKind::Call {
                    func,
                    substs,
                    destination,
                    target: *target,
                    args: args
                        .iter()
                        .map(|arg| {
                            self.lower_operand(arg).map_err(|reason| {
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
            rustc_mir::TerminatorKind::Resume => TerminatorKind::Resume,
            rustc_mir::TerminatorKind::Terminate
            | rustc_mir::TerminatorKind::Yield { .. }
            | rustc_mir::TerminatorKind::GeneratorDrop
            | rustc_mir::TerminatorKind::InlineAsm { .. } => {
                return Err(errors::UnsupportedMir::from(terminator)).emit(self.sess);
            }
        };
        Ok(Terminator { kind, source_info: terminator.source_info })
    }

    fn resolve_call(
        &self,
        callee_id: DefId,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Result<(DefId, CallSubsts<'tcx>), UnsupportedReason> {
        // NOTE(nilehmann) tcx.resolve_instance used to panic without this check but none of the tests
        // are failing now. Leaving it here in case the problem comes back.
        // if substs.needs_infer() {
        //     return Ok(None);
        // }

        // this produced erased regions in the substitution for early bound regions
        let param_env = self.tcx.param_env(self.rustc_mir.source.def_id());
        let (resolved_id, resolved_substs) = self
            .tcx
            .resolve_instance(param_env.and((callee_id, substs)))
            .ok()
            .flatten()
            .map_or_else(|| (callee_id, substs), |instance| (instance.def_id(), instance.args));

        let call_substs = CallSubsts {
            lowered: lower_generic_args(self.tcx, resolved_substs)?,
            orig: resolved_substs,
        };
        Ok((resolved_id, call_substs))
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
            rustc_mir::Rvalue::CheckedBinaryOp(bin_op, box (op1, op2)) => {
                Ok(Rvalue::CheckedBinaryOp(
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
                let kind = self
                    .lower_cast_kind(*kind)
                    .ok_or_else(|| UnsupportedReason::new("unsupported cast"))?;
                let op = self.lower_operand(op)?;
                let ty = lower_ty(self.tcx, *ty)?;
                Ok(Rvalue::Cast(kind, op, ty))
            }
            rustc_mir::Rvalue::Repeat(_, _)
            | rustc_mir::Rvalue::ThreadLocalRef(_)
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
            rustc_mir::BorrowKind::Shallow => {
                Err(UnsupportedReason::new(format!("unsupported borrow kind `{bk:?}`")))
            }
        }
    }

    fn lower_cast_kind(&self, kind: rustc_mir::CastKind) -> Option<CastKind> {
        match kind {
            rustc_mir::CastKind::IntToInt => Some(CastKind::IntToInt),
            rustc_mir::CastKind::IntToFloat => Some(CastKind::IntToFloat),
            rustc_mir::CastKind::FloatToInt => Some(CastKind::FloatToInt),
            rustc_mir::CastKind::PointerCoercion(
                rustc_adjustment::PointerCoercion::MutToConstPointer,
            ) => Some(CastKind::Pointer(crate::rustc::mir::PointerCast::MutToConstPointer)),
            _ => None,
        }
    }

    fn lower_aggregate_kind(
        &self,
        aggregate_kind: &rustc_mir::AggregateKind<'tcx>,
    ) -> Result<AggregateKind, UnsupportedReason> {
        match aggregate_kind {
            rustc_mir::AggregateKind::Adt(def_id, variant_idx, substs, None, None) => {
                Ok(AggregateKind::Adt(*def_id, *variant_idx, lower_generic_args(self.tcx, substs)?))
            }
            rustc_mir::AggregateKind::Array(ty) => {
                Ok(AggregateKind::Array(lower_ty(self.tcx, *ty)?))
            }
            rustc_mir::AggregateKind::Tuple => Ok(AggregateKind::Tuple),
            rustc_mir::AggregateKind::Closure(did, substs) => {
                let lowered_substs = lower_generic_args(self.tcx, substs)?;
                Ok(AggregateKind::Closure(*did, lowered_substs))
            }
            rustc_mir::AggregateKind::Adt(..) | rustc_mir::AggregateKind::Generator(_, _, _) => {
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
            rustc_mir::BinOp::Shl => Ok(BinOp::Shl),
            rustc_mir::BinOp::Shr => Ok(BinOp::Shr),
            rustc_mir::BinOp::AddUnchecked
            | rustc_mir::BinOp::SubUnchecked
            | rustc_mir::BinOp::MulUnchecked
            | rustc_mir::BinOp::ShlUnchecked
            | rustc_mir::BinOp::ShrUnchecked
            | rustc_mir::BinOp::BitXor
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
        constant: &rustc_mir::Constant<'tcx>,
    ) -> Result<Constant, UnsupportedReason> {
        use rustc_middle::ty::TyKind;
        // use rustc_ty::ScalarInt;
        use rustc_mir::interpret::Scalar;
        use rustc_mir::ConstantKind;
        let tcx = self.tcx;

        // HACK(nilehmann) we evaluate the constant to support u32::MAX
        // we should instead lower it as is and refine its type.
        let kind = constant.literal.eval(tcx, ParamEnv::empty());
        match (kind, constant.ty().kind()) {
            (ConstantKind::Val(ConstValue::Scalar(Scalar::Int(scalar)), ty), _) => {
                scalar_int_to_constant(tcx, scalar, ty)
            }
            (ConstantKind::Val(ConstValue::Slice { .. }, _), TyKind::Ref(_, ref_ty, _))
                if ref_ty.is_str() =>
            {
                Some(Constant::Str)
            }
            (ConstantKind::Ty(c), _) => {
                if let rustc_ty::ConstKind::Value(rustc_ty::ValTree::Leaf(scalar)) = c.kind() {
                    scalar_int_to_constant(tcx, scalar, c.ty())
                } else {
                    None
                }
            }
            (_, TyKind::Tuple(tys)) if tys.is_empty() => return Ok(Constant::Unit),
            _ => None,
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

impl UnsupportedReason {
    fn new(reason: impl ToString) -> Self {
        UnsupportedReason { descr: reason.to_string() }
    }
}

/// [NOTE:Fake Predecessors] The `FalseEdge/imaginary_target` edges mess up
/// the `is_join_point` computation which creates spurious join points that
/// lose information e.g. in match arms, the k+1-th arm has the k-th arm as
/// a "fake" predecessor so we lose the assumptions specific to the k+1-th
/// arm due to a spurious join. This code corrects for this problem by
/// computing the number of "fake" predecessors and decreasing them from
/// the total number of "predecessors" returned by `rustc`.
/// The option is to recompute "predecessors" from scratch but we may miss
/// some cases there. (see also [`is_join_point`])
///
/// [`is_join_point`]: crate::rustc::mir::Body::is_join_point
fn mk_fake_predecessors(
    basic_blocks: &IndexVec<BasicBlock, BasicBlockData>,
) -> IndexVec<BasicBlock, usize> {
    let mut res: IndexVec<BasicBlock, usize> = basic_blocks.iter().map(|_| 0).collect();

    for bb in basic_blocks {
        if let Some(terminator) = &bb.terminator {
            if let TerminatorKind::FalseEdge { imaginary_target, .. } = terminator.kind {
                res[imaginary_target] += 1;
            }
        }
    }
    res
}

pub(crate) fn lower_fn_sig<'tcx>(
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
                vars.push(BoundVariableKind::Region(lower_bound_region_kind(*kind)?));
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
        rustc_ty::Adt(adt_def, substs) => {
            let substs = lower_generic_args(tcx, substs)?;
            Ok(Ty::mk_adt(lower_adt_def(adt_def), substs))
        }
        rustc_ty::Never => Ok(Ty::mk_never()),
        rustc_ty::Str => Ok(Ty::mk_str()),
        rustc_ty::Char => Ok(Ty::mk_char()),
        rustc_ty::Tuple(tys) => {
            let tys = List::from_vec(tys.iter().map(|ty| lower_ty(tcx, ty)).try_collect()?);
            Ok(Ty::mk_tuple(tys))
        }
        rustc_ty::Array(ty, len) => {
            let len = len
                .to_valtree()
                .try_to_target_usize(tcx)
                .ok_or_else(|| UnsupportedReason::new(format!("unsupported array len {len:?}")))?;
            Ok(Ty::mk_array(lower_ty(tcx, *ty)?, Const { val: len as usize }))
        }
        rustc_ty::Slice(ty) => Ok(Ty::mk_slice(lower_ty(tcx, *ty)?)),
        rustc_ty::RawPtr(t) => {
            let mutbl = t.mutbl;
            let ty = lower_ty(tcx, t.ty)?;
            Ok(Ty::mk_raw_ptr(ty, mutbl))
        }
        rustc_ty::FnPtr(fn_sig) => {
            let fn_sig = lower_fn_sig(tcx, *fn_sig)?;
            Ok(Ty::mk_fn_ptr(fn_sig))
        }
        rustc_ty::Closure(did, substs) => {
            let substs = lower_generic_args(tcx, substs)?;
            Ok(Ty::mk_closure(*did, substs))
        }

        rustc_ty::Alias(kind, alias_ty) => {
            let kind = lower_alias_kind(kind)?;
            let substs = lower_generic_args(tcx, alias_ty.args)?;
            Ok(Ty::mk_alias(kind, alias_ty.def_id, substs))
        }

        _ => Err(UnsupportedReason::new(format!("unsupported type `{ty:?}`"))),
    }
}

fn lower_alias_kind(kind: &rustc_ty::AliasKind) -> Result<AliasKind, UnsupportedReason> {
    match kind {
        rustc_type_ir::AliasKind::Projection => Ok(AliasKind::Projection),
        rustc_type_ir::AliasKind::Opaque => Ok(AliasKind::Opaque),
        _ => Err(UnsupportedReason::new(format!("unsupported alias kind `{kind:?}`"))),
    }
}

pub fn lower_adt_def(adt_def: &rustc_ty::AdtDef) -> AdtDef {
    AdtDef::new(AdtDefData::new(
        adt_def.did(),
        adt_def.variants().iter().map(lower_variant).collect(),
        adt_def.flags(),
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

fn lower_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Result<List<GenericArg>, UnsupportedReason> {
    Ok(List::from_vec(
        substs
            .iter()
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
        GenericArgKind::Const(_) => {
            Err(UnsupportedReason::new(format!("unsupported generic const `{arg:?}`")))
        }
    }
}

fn lower_region(region: &rustc_middle::ty::Region) -> Result<Region, UnsupportedReason> {
    use rustc_middle::ty::RegionKind;
    match region.kind() {
        RegionKind::ReVar(id) => Ok(Region::ReVar(RegionVar { rvid: id, is_nll: true })),
        RegionKind::ReLateBound(debruijn, bregion) => {
            Ok(Region::ReLateBound(debruijn, lower_bound_region(bregion)?))
        }
        RegionKind::ReEarlyBound(bregion) => Ok(Region::ReEarlyBound(bregion)),
        RegionKind::ReErased => Ok(Region::ReErased),
        RegionKind::ReStatic => Ok(Region::ReStatic),
        RegionKind::ReFree(_) | RegionKind::RePlaceholder(_) | RegionKind::ReError(_) => {
            Err(UnsupportedReason::new(format!("unsupported region `{region:?}`")))
        }
    }
}

fn lower_bound_region(
    bregion: rustc_middle::ty::BoundRegion,
) -> Result<BoundRegion, UnsupportedReason> {
    Ok(BoundRegion { kind: lower_bound_region_kind(bregion.kind)?, var: bregion.var })
}

fn lower_bound_region_kind(
    kind: rustc_middle::ty::BoundRegionKind,
) -> Result<BoundRegionKind, UnsupportedReason> {
    match kind {
        rustc_ty::BoundRegionKind::BrNamed(def_id, sym) => {
            Ok(BoundRegionKind::BrNamed(def_id, sym))
        }
        rustc_ty::BoundRegionKind::BrAnon(_) => Ok(BoundRegionKind::BrAnon),
        _ => Err(UnsupportedReason::new(format!("unsupported bound region kind `{kind:?}`"))),
    }
}

pub fn lower_generics(generics: &rustc_ty::Generics) -> Result<Generics, UnsupportedReason> {
    let params = List::from_vec(
        generics
            .params
            .iter()
            .map(lower_generic_param_def)
            .try_collect()?,
    );
    Ok(Generics { params, orig: generics })
}

fn lower_generic_param_def(
    generic: &rustc_ty::GenericParamDef,
) -> Result<GenericParamDef, UnsupportedReason> {
    let kind = match generic.kind {
        rustc_ty::GenericParamDefKind::Type { has_default, synthetic: false } => {
            GenericParamDefKind::Type { has_default }
        }
        rustc_ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
        _ => return Err(UnsupportedReason::new("unsupported generic param")),
    };
    Ok(GenericParamDef { def_id: generic.def_id, index: generic.index, name: generic.name, kind })
}

#[allow(clippy::mutable_key_type)] // False positive `List` is not mutable
pub(crate) fn lower_generic_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    sess: &FluxSession,
    generics: rustc_ty::GenericPredicates<'tcx>,
) -> Result<GenericPredicates, ErrorGuaranteed> {
    let mut fn_trait_refs = FxHashMap::default();
    let mut fn_output_proj = FxHashMap::default();
    let mut predicates = vec![];

    for (predicate, span) in generics.predicates {
        let bound_vars = predicate.kind().bound_vars();
        let kind = predicate.kind().skip_binder();

        match kind {
            rustc_ty::ClauseKind::Trait(trait_pred) => {
                let trait_ref = trait_pred.trait_ref;
                let substs = rustc_ty::Binder::bind_with_vars(trait_ref.args, bound_vars);
                if let Some(closure_kind) = tcx.fn_trait_kind_from_def_id(trait_ref.def_id) {
                    match fn_trait_refs.entry(substs) {
                        hash_map::Entry::Occupied(_) => todo!(),
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert((closure_kind, *span));
                        }
                    }
                }
            }
            rustc_ty::ClauseKind::Projection(proj_pred) => {
                let proj_ty = proj_pred.projection_ty;
                let substs = rustc_ty::Binder::bind_with_vars(proj_ty.args, bound_vars);
                if proj_ty.def_id == tcx.lang_items().fn_once_output().unwrap() {
                    match fn_output_proj.entry(substs) {
                        hash_map::Entry::Occupied(_) => todo!(),
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(proj_pred.term.ty().unwrap());
                        }
                    };
                } else if let Some(ty) = proj_pred.term.ty() &&
                          let Some(substs) = substs.no_bound_vars(){
                    let substs = lower_generic_args(tcx, substs)
                        .map_err(|err| errors::UnsupportedGenericBound::new(*span, err.descr))
                        .emit(sess)?;

                    let projection_ty = AliasTy { substs, def_id: proj_ty.def_id };
                    let term = lower_ty(tcx, ty)
                        .map_err(|err| errors::UnsupportedGenericBound::new(*span, err.descr))
                        .emit(sess)?;
                    let kind = ClauseKind::Projection(ProjectionPredicate { projection_ty, term });
                    predicates.push(Clause::new(Binder::bind_with_vars(kind, List::empty())));
                }
            }
            _ => {}
        }
    }

    for (substs, (kind, span)) in fn_trait_refs {
        let output = fn_output_proj.get(&substs).unwrap();

        let vars = substs.bound_vars();
        let substs = substs.skip_binder().into_type_list(tcx);
        let bounded_ty = lower_ty(tcx, substs[0])
            .map_err(|err| errors::UnsupportedGenericBound::new(span, err.descr))
            .emit(sess)?;
        let tupled_args = lower_ty(tcx, substs[1])
            .map_err(|err| errors::UnsupportedGenericBound::new(span, err.descr))
            .emit(sess)?;
        let output = lower_ty(tcx, *output)
            .map_err(|err| errors::UnsupportedGenericBound::new(span, err.descr))
            .emit(sess)?;

        let vars = lower_bound_vars(vars)
            .map_err(|err| errors::UnsupportedGenericBound::new(span, err.descr))
            .emit(sess)?;

        let kind = ClauseKind::FnTrait { bounded_ty, tupled_args, output, kind };
        predicates.push(Clause::new(Binder::bind_with_vars(kind, vars)));
    }
    Ok(GenericPredicates { parent: generics.parent, predicates: List::from_vec(predicates) })
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_middle::mir as rustc_mir;
    use rustc_span::Span;

    use super::UnsupportedReason;

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_local_decl, code = "FLUX")]
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
            println!("TRACE: unsupported local_decl {local_decl:?} {_err:?}");
            Self { span: local_decl.source_info.span, ty: local_decl.ty }
        }
    }

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_mir, code = "FLUX")]
    #[note]
    pub(super) struct UnsupportedMir {
        #[primary_span]
        span: Span,
        kind: &'static str,
        reason: UnsupportedReason,
    }

    impl rustc_errors::IntoDiagnosticArg for UnsupportedReason {
        fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
            rustc_errors::DiagnosticArgValue::Str(std::borrow::Cow::Owned(self.descr))
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
                UnsupportedReason::new(format!("{terminator:?}")),
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

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_generic_bound, code = "FLUX")]
    #[note]
    pub struct UnsupportedGenericBound {
        #[primary_span]
        span: Span,
        reason: String,
    }

    impl UnsupportedGenericBound {
        pub fn new(span: Span, reason: impl ToString) -> Self {
            Self { span, reason: reason.to_string() }
        }
    }
}
