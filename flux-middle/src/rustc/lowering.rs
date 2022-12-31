pub use errors::UnsupportedFnSig;
use flux_common::index::IndexVec;
use flux_errors::{FluxSession, ResultExt};
use itertools::Itertools;
use rustc_const_eval::interpret::ConstValue;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir as rustc_mir,
    ty::{
        self as rustc_ty,
        subst::{GenericArgKind, SubstsRef},
        ParamEnv, TyCtxt, TypeVisitable,
    },
};
use rustc_trait_selection::traits::NormalizeExt;

use super::{
    mir::{
        AggregateKind, AssertKind, BasicBlock, BasicBlockData, BinOp, Body, CallSubsts, CastKind,
        Constant, FakeReadCause, Instance, LocalDecl, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        AdtDef, Binder, BoundRegion, BoundRegionKind, BoundVariableKind, Const, FnSig, GenericArg,
        GenericParamDef, GenericParamDefKind, Generics, PolyFnSig, Ty, VariantDef,
    },
};
use crate::{intern::List, rustc::ty::Region};

pub struct LoweringCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    rustc_mir: rustc_mir::Body<'tcx>,
}

pub struct UnsupportedType {
    pub reason: String,
}

impl<'a, 'tcx> LoweringCtxt<'a, 'tcx> {
    pub fn lower_mir_body(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        rustc_mir: rustc_mir::Body<'tcx>,
    ) -> Result<Body<'tcx>, ErrorGuaranteed> {
        let lower = Self { tcx, sess, rustc_mir };

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

        Ok(Body { basic_blocks, local_decls, fake_predecessors, rustc_mir: lower.rustc_mir })
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
                    self.lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    self.lower_rvalue(rvalue)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )
            }
            rustc_mir::StatementKind::SetDiscriminant { place, variant_index } => {
                StatementKind::SetDiscriminant(
                    self.lower_place(place)
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
                    self.lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                )))
            }
            rustc_mir::StatementKind::Nop
            | rustc_mir::StatementKind::StorageLive(_)
            | rustc_mir::StatementKind::StorageDead(_) => StatementKind::Nop,
            rustc_mir::StatementKind::AscribeUserType(
                box (place, rustc_mir::UserTypeProjection { projs, .. }),
                variance,
            ) if projs.is_empty() => {
                StatementKind::AscribeUserType(
                    self.lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::statement(span, reason))
                        .emit(self.sess)?,
                    *variance,
                )
            }
            rustc_mir::StatementKind::Retag(_, _)
            | rustc_mir::StatementKind::Deinit(_)
            | rustc_mir::StatementKind::AscribeUserType(..)
            | rustc_mir::StatementKind::Coverage(_)
            | rustc_mir::StatementKind::Intrinsic(_) => {
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
            rustc_mir::TerminatorKind::Call {
                func, args, destination, target, cleanup, ..
            } => {
                let (func, substs) = match func.ty(&self.rustc_mir, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, substs) => {
                        let lowered_substs = lower_substs(self.tcx, substs)
                            .map_err(|_| errors::UnsupportedMir::from(terminator))
                            .emit(self.sess)?;
                        (*fn_def, CallSubsts { orig: substs, lowered: lowered_substs })
                    }
                    _ => Err(errors::UnsupportedMir::from(terminator)).emit(self.sess)?,
                };

                let destination = self
                    .lower_place(destination)
                    .map_err(|reason| errors::UnsupportedMir::new(span, "terminator", reason))
                    .emit(self.sess)?;

                let instance = self
                    .lower_instance(func, substs.orig)
                    .map_err(|_| errors::UnsupportedMir::from(terminator))
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
                                errors::UnsupportedMir::new(span, "terminator", reason)
                            })
                        })
                        .try_collect()
                        .emit(self.sess)?,
                    cleanup: *cleanup,
                    instance,
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
            rustc_mir::TerminatorKind::Drop { place, target, unwind } => {
                TerminatorKind::Drop {
                    place: self
                        .lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    target: *target,
                    unwind: *unwind,
                }
            }
            rustc_mir::TerminatorKind::DropAndReplace { place, value, target, unwind } => {
                TerminatorKind::DropAndReplace {
                    place: self
                        .lower_place(place)
                        .map_err(|reason| errors::UnsupportedMir::terminator(span, reason))
                        .emit(self.sess)?,
                    value: self
                        .lower_operand(value)
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
            rustc_mir::TerminatorKind::Abort
            | rustc_mir::TerminatorKind::Yield { .. }
            | rustc_mir::TerminatorKind::GeneratorDrop
            | rustc_mir::TerminatorKind::InlineAsm { .. } => {
                return Err(errors::UnsupportedMir::from(terminator)).emit(self.sess);
            }
        };
        Ok(Terminator { kind, source_info: terminator.source_info })
    }

    fn lower_instance(
        &self,
        trait_f: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Result<Option<Instance>, UnsupportedType> {
        // tcx.resolve_instance panics without this check
        if substs.needs_infer() {
            return Ok(None);
        }

        let param_env = self.tcx.param_env(self.rustc_mir.source.def_id());
        match self.tcx.resolve_instance(param_env.and((trait_f, substs))) {
            Ok(Some(instance)) => {
                let impl_f = instance.def_id();
                if impl_f == trait_f {
                    Ok(None)
                } else {
                    let substs = lower_substs(self.tcx, instance.substs)?;
                    Ok(Some(Instance { impl_f, substs }))
                }
            }
            _ => Ok(None),
        }
    }

    fn lower_rvalue(&self, rvalue: &rustc_mir::Rvalue<'tcx>) -> Result<Rvalue, String> {
        match rvalue {
            rustc_mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            rustc_mir::Rvalue::BinaryOp(bin_op, operands) => {
                Ok(Rvalue::BinaryOp(
                    self.lower_bin_op(*bin_op)?,
                    self.lower_operand(&operands.0)?,
                    self.lower_operand(&operands.1)?,
                ))
            }
            rustc_mir::Rvalue::Ref(_, rustc_mir::BorrowKind::Mut { .. }, p) => {
                Ok(Rvalue::MutRef(self.lower_place(p)?))
            }
            rustc_mir::Rvalue::Ref(_, rustc_mir::BorrowKind::Shared, p) => {
                Ok(Rvalue::ShrRef(self.lower_place(p)?))
            }
            rustc_mir::Rvalue::UnaryOp(un_op, op) => {
                Ok(Rvalue::UnaryOp(*un_op, self.lower_operand(op)?))
            }
            rustc_mir::Rvalue::Aggregate(aggregate_kind, args) => {
                let aggregate_kind = self.lower_aggregate_kind(aggregate_kind)?;
                let args = args.iter().map(|op| self.lower_operand(op)).try_collect()?;
                Ok(Rvalue::Aggregate(aggregate_kind, args))
            }
            rustc_mir::Rvalue::Discriminant(p) => Ok(Rvalue::Discriminant(self.lower_place(p)?)),
            rustc_mir::Rvalue::Len(place) => Ok(Rvalue::Len(self.lower_place(place)?)),
            rustc_mir::Rvalue::Cast(kind, op, ty) => {
                let kind = self.lower_cast_kind(*kind).ok_or("unsupported cast")?;
                let op = self.lower_operand(op)?;
                let ty = lower_ty(self.tcx, *ty).map_err(|err| err.reason)?;
                Ok(Rvalue::Cast(kind, op, ty))
            }
            rustc_mir::Rvalue::Repeat(_, _)
            | rustc_mir::Rvalue::Ref(_, _, _)
            | rustc_mir::Rvalue::ThreadLocalRef(_)
            | rustc_mir::Rvalue::AddressOf(_, _)
            | rustc_mir::Rvalue::CheckedBinaryOp(_, _)
            | rustc_mir::Rvalue::NullaryOp(_, _)
            | rustc_mir::Rvalue::CopyForDeref(_)
            | rustc_mir::Rvalue::ShallowInitBox(_, _) => {
                Err(format!("unsupported rvalue `{rvalue:?}`"))
            }
        }
    }

    fn lower_cast_kind(&self, kind: rustc_mir::CastKind) -> Option<CastKind> {
        match kind {
            rustc_mir::CastKind::IntToInt => Some(CastKind::IntToInt),
            rustc_mir::CastKind::IntToFloat => Some(CastKind::IntToFloat),
            rustc_mir::CastKind::FloatToInt => Some(CastKind::FloatToInt),
            _ => None,
        }
    }

    fn lower_aggregate_kind(
        &self,
        aggregate_kind: &rustc_mir::AggregateKind<'tcx>,
    ) -> Result<AggregateKind, String> {
        match aggregate_kind {
            rustc_mir::AggregateKind::Adt(def_id, variant_idx, substs, None, None) => {
                Ok(AggregateKind::Adt(
                    *def_id,
                    *variant_idx,
                    lower_substs(self.tcx, substs).map_err(|err| err.reason)?,
                ))
            }
            rustc_mir::AggregateKind::Array(ty) => {
                Ok(AggregateKind::Array(lower_ty(self.tcx, *ty).map_err(|err| err.reason)?))
            }
            rustc_mir::AggregateKind::Tuple => Ok(AggregateKind::Tuple),
            rustc_mir::AggregateKind::Adt(..)
            | rustc_mir::AggregateKind::Closure(_, _)
            | rustc_mir::AggregateKind::Generator(_, _, _) => {
                Err(format!("unsupported aggregate kind `{aggregate_kind:?}`"))
            }
        }
    }

    fn lower_bin_op(&self, bin_op: rustc_mir::BinOp) -> Result<BinOp, String> {
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
            rustc_mir::BinOp::BitXor
            | rustc_mir::BinOp::BitOr
            | rustc_mir::BinOp::Shl
            | rustc_mir::BinOp::Shr
            | rustc_mir::BinOp::Offset => Err(format!("unsupported binary op `{bin_op:?}`")),
        }
    }

    fn lower_operand(&self, op: &rustc_mir::Operand<'tcx>) -> Result<Operand, String> {
        match op {
            rustc_mir::Operand::Copy(place) => Ok(Operand::Copy(self.lower_place(place)?)),
            rustc_mir::Operand::Move(place) => Ok(Operand::Move(self.lower_place(place)?)),
            rustc_mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
        }
    }

    fn lower_place(&self, place: &rustc_mir::Place<'tcx>) -> Result<Place, String> {
        let mut projection = vec![];
        for elem in place.projection {
            match elem {
                rustc_mir::PlaceElem::Deref => projection.push(PlaceElem::Deref),
                rustc_mir::PlaceElem::Field(field, _) => projection.push(PlaceElem::Field(field)),
                rustc_mir::PlaceElem::Downcast(_, variant_idx) => {
                    projection.push(PlaceElem::Downcast(variant_idx));
                }
                rustc_mir::PlaceElem::Index(v) => projection.push(PlaceElem::Index(v)),
                _ => {
                    return Err(format!("unsupported place `{place:?}`"));
                }
            }
        }
        Ok(Place { local: place.local, projection })
    }

    fn lower_constant(&self, constant: &rustc_mir::Constant<'tcx>) -> Result<Constant, String> {
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
        .ok_or_else(|| format!("unsupported constant `{constant:?}`"))
    }

    fn lower_assert_msg(&self, msg: &rustc_mir::AssertMessage) -> Option<AssertKind> {
        use rustc_mir::AssertKind::*;
        match msg {
            BoundsCheck { .. } => Some(AssertKind::BoundsCheck),
            DivisionByZero(_) => Some(AssertKind::Other("possible division by zero")),
            RemainderByZero(_) => {
                Some(AssertKind::Other("possible remainder with a divisor of zero"))
            }
            Overflow(rustc_mir::BinOp::Div, _, _) => {
                Some(AssertKind::Other("possible division with overflow"))
            }
            Overflow(rustc_mir::BinOp::Rem, _, _) => {
                Some(AssertKind::Other("possible remainder with overflow"))
            }
            _ => None,
        }
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

pub fn lower_type_of(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: DefId,
) -> Result<Ty, ErrorGuaranteed> {
    let span = tcx.def_span(def_id);
    let ty = tcx.type_of(def_id);
    lower_ty(tcx, ty)
        .map_err(|err| errors::UnsupportedTypeOf::new(span, ty, err))
        .emit(sess)
}

pub fn lower_adt_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    sess: &FluxSession,
    adt_def: rustc_ty::AdtDef<'tcx>,
) -> Result<AdtDef, ErrorGuaranteed> {
    let adt_def_id = adt_def.did();
    let mut variants = vec![];
    for variant_def in adt_def.variants() {
        variants.push(lower_variant_def(tcx, sess, adt_def_id, variant_def)?);
    }
    Ok(AdtDef { variants })
}

pub fn lower_variant_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    adt_def_id: DefId,
    variant_def: &rustc_ty::VariantDef,
) -> Result<VariantDef, ErrorGuaranteed> {
    let field_tys = List::from_vec(
        variant_def
            .fields
            .iter()
            .map(|field| lower_type_of(tcx, sess, field.did))
            .try_collect()?,
    );
    let fields = variant_def.fields.iter().map(|fld| fld.did).collect_vec();
    let ret = lower_type_of(tcx, sess, adt_def_id)?;
    Ok(VariantDef { field_tys, fields, ret, def_id: variant_def.def_id })
}

pub fn lower_fn_sig_of(tcx: TyCtxt, def_id: DefId) -> Result<PolyFnSig, errors::UnsupportedFnSig> {
    let fn_sig = tcx.fn_sig(def_id);
    let span = tcx.def_span(def_id);
    let param_env = tcx.param_env(def_id);
    let result = tcx
        .infer_ctxt()
        .build()
        .at(&rustc_middle::traits::ObligationCause::dummy(), param_env)
        .normalize(fn_sig);
    lower_fn_sig(tcx, result.value)
        .map_err(|err| errors::UnsupportedFnSig { span, reason: err.reason })
}

fn lower_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_sig: rustc_ty::PolyFnSig<'tcx>,
) -> Result<PolyFnSig, UnsupportedType> {
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
    mut f: impl FnMut(S) -> Result<T, UnsupportedType>,
) -> Result<Binder<T>, UnsupportedType> {
    let mut vars = vec![];
    for var in binder.bound_vars() {
        match var {
            rustc_ty::BoundVariableKind::Region(kind) => {
                vars.push(BoundVariableKind::Region(lower_bound_region_kind(kind)?))
            }
            _ => {
                return Err(UnsupportedType {
                    reason: format!("unsupported bound variable {var:?}"),
                });
            }
        }
    }
    Ok(Binder::bind_with_vars(f(binder.skip_binder())?, vars))
}

pub fn lower_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_ty::Ty<'tcx>) -> Result<Ty, UnsupportedType> {
    match ty.kind() {
        rustc_ty::Ref(_region, ty, mutability) => Ok(Ty::mk_ref(lower_ty(tcx, *ty)?, *mutability)),
        rustc_ty::Bool => Ok(Ty::mk_bool()),
        rustc_ty::Int(int_ty) => Ok(Ty::mk_int(*int_ty)),
        rustc_ty::Uint(uint_ty) => Ok(Ty::mk_uint(*uint_ty)),
        rustc_ty::Float(float_ty) => Ok(Ty::mk_float(*float_ty)),
        rustc_ty::Param(param_ty) => Ok(Ty::mk_param(*param_ty)),
        rustc_ty::Adt(adt_def, substs) => {
            let substs = List::from_vec(
                substs
                    .iter()
                    .map(|arg| lower_generic_arg(tcx, arg))
                    .try_collect()?,
            );
            Ok(Ty::mk_adt(adt_def.did(), substs))
        }
        rustc_ty::Never => Ok(Ty::mk_never()),
        rustc_ty::Str => Ok(Ty::mk_str()),
        rustc_ty::Char => Ok(Ty::mk_char()),
        rustc_ty::Tuple(tys) => {
            let tys = List::from_vec(tys.iter().map(|ty| lower_ty(tcx, ty)).try_collect()?);
            Ok(Ty::mk_tuple(tys))
        }
        rustc_ty::Array(ty, len) => {
            // TODO(RJ) https://github.com/liquid-rust/flux/pull/255#discussion_r1052554570
            let param_env = ParamEnv::empty().with_reveal_all_normalized(tcx);
            let val = len
                .try_eval_usize(tcx, param_env)
                .unwrap_or_else(|| panic!("failed to evaluate array length: {len:?} in {ty:?}"))
                as usize;
            Ok(Ty::mk_array(lower_ty(tcx, *ty)?, Const { val }))
        }
        rustc_ty::Slice(ty) => Ok(Ty::mk_slice(lower_ty(tcx, *ty)?)),
        _ => Err(UnsupportedType { reason: format!("TRACE unsupported type `{ty:?}`") }),
    }
}

fn lower_substs<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<List<GenericArg>, UnsupportedType> {
    Ok(List::from_vec(
        substs
            .iter()
            .map(|arg| lower_generic_arg(tcx, arg))
            .try_collect()?,
    ))
}

fn lower_generic_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    arg: rustc_middle::ty::subst::GenericArg<'tcx>,
) -> Result<GenericArg, UnsupportedType> {
    match arg.unpack() {
        GenericArgKind::Type(ty) => Ok(GenericArg::Ty(lower_ty(tcx, ty)?)),
        GenericArgKind::Lifetime(region) => Ok(GenericArg::Lifetime(lower_region(&region)?)),
        GenericArgKind::Const(_) => {
            Err(UnsupportedType { reason: format!("unsupported generic const `{arg:?}`") })
        }
    }
}

fn lower_region(region: &rustc_middle::ty::Region) -> Result<Region, UnsupportedType> {
    use rustc_middle::ty::RegionKind;
    match region.kind() {
        RegionKind::ReVar(rvid) => Ok(Region::ReVar(rvid)),
        RegionKind::ReLateBound(debruijn, bregion) => {
            Ok(Region::ReLateBound(debruijn, lower_bound_region(bregion)?))
        }
        RegionKind::ReEarlyBound(bregion) => Ok(Region::ReEarlyBound(bregion)),
        RegionKind::ReFree(_)
        | RegionKind::ReStatic
        | RegionKind::RePlaceholder(_)
        | RegionKind::ReErased => {
            Err(UnsupportedType { reason: format!("unsupported region `{region:?}`") })
        }
    }
}

fn lower_bound_region(
    bregion: rustc_middle::ty::BoundRegion,
) -> Result<BoundRegion, UnsupportedType> {
    Ok(BoundRegion { kind: lower_bound_region_kind(bregion.kind)?, var: bregion.var })
}

fn lower_bound_region_kind(
    kind: rustc_middle::ty::BoundRegionKind,
) -> Result<BoundRegionKind, UnsupportedType> {
    match kind {
        rustc_ty::BoundRegionKind::BrNamed(def_id, sym) => {
            Ok(BoundRegionKind::BrNamed(def_id, sym))
        }
        _ => Err(UnsupportedType { reason: format!("unsupported boudn region kind `{kind:?}`") }),
    }
}

pub fn lower_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    sess: &FluxSession,
    generics: &'tcx rustc_ty::Generics,
) -> Result<Generics<'tcx>, ErrorGuaranteed> {
    let params = List::from_vec(
        generics
            .params
            .iter()
            .map(|generic| lower_generic_param_def(tcx, sess, generic))
            .try_collect()?,
    );
    Ok(Generics { params, rustc: generics })
}

fn lower_generic_param_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    generic: &rustc_ty::GenericParamDef,
) -> Result<GenericParamDef, ErrorGuaranteed> {
    let kind = match generic.kind {
        rustc_ty::GenericParamDefKind::Type { has_default, synthetic: false } => {
            GenericParamDefKind::Type { has_default }
        }
        rustc_ty::GenericParamDefKind::Lifetime => GenericParamDefKind::Lifetime,
        _ => {
            return Err(errors::UnsupportedGenericParam::new(tcx.def_span(generic.def_id)))
                .emit(sess);
        }
    };
    Ok(GenericParamDef { def_id: generic.def_id, index: generic.index, name: generic.name, kind })
}

fn scalar_int_to_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Constant> {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Int(int_ty) => {
            Some(Constant::Int(scalar_to_int(tcx, scalar, ty).unwrap(), *int_ty))
        }
        TyKind::Uint(int_ty) => {
            Some(Constant::Uint(scalar_to_uint(tcx, scalar, ty).unwrap(), *int_ty))
        }
        TyKind::Float(float_ty) => {
            Some(Constant::Float(scalar_to_bits(tcx, scalar, ty).unwrap(), *float_ty))
        }
        TyKind::Char => Some(Constant::Char),
        TyKind::Bool => Some(Constant::Bool(scalar_to_bits(tcx, scalar, ty).unwrap() != 0)),
        TyKind::Tuple(tys) if tys.is_empty() => Some(Constant::Unit),
        _ => None,
    }
}

fn scalar_to_bits<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.to_bits(size).ok()
}

fn scalar_to_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_ty::Ty<'tcx>,
) -> Option<i128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.try_to_int(size).ok()
}

fn scalar_to_uint<'tcx>(
    tcx: TyCtxt<'tcx>,
    scalar: rustc_ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<u128> {
    let size = tcx
        .layout_of(ParamEnv::empty().with_reveal_all_normalized(tcx).and(ty))
        .unwrap()
        .size;
    scalar.try_to_uint(size).ok()
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_middle::mir as rustc_mir;
    use rustc_span::Span;

    use super::UnsupportedType;

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_local_decl, code = "FLUX")]
    pub struct UnsupportedLocalDecl<'tcx> {
        #[primary_span]
        #[label]
        span: Span,
        ty: rustc_middle::ty::Ty<'tcx>,
    }

    impl<'tcx> UnsupportedLocalDecl<'tcx> {
        pub fn new(local_decl: &rustc_mir::LocalDecl<'tcx>, _err: UnsupportedType) -> Self {
            Self { span: local_decl.source_info.span, ty: local_decl.ty }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_mir, code = "FLUX")]
    #[note]
    pub struct UnsupportedMir {
        #[primary_span]
        pub span: Span,
        pub kind: &'static str,
        pub reason: String,
    }

    impl UnsupportedMir {
        pub fn new(span: Span, kind: &'static str, reason: String) -> Self {
            Self { span, kind, reason }
        }

        pub fn terminator(span: Span, reason: String) -> Self {
            Self { span, kind: "terminator", reason }
        }

        pub fn statement(span: Span, reason: String) -> Self {
            Self { span, kind: "statement", reason }
        }
    }

    impl<'a, 'tcx> From<&'a rustc_mir::Terminator<'tcx>> for UnsupportedMir {
        fn from(terminator: &'a rustc_mir::Terminator<'tcx>) -> Self {
            Self::terminator(terminator.source_info.span, format!("{terminator:?}"))
        }
    }

    impl<'a, 'tcx> From<&'a rustc_mir::Statement<'tcx>> for UnsupportedMir {
        fn from(statement: &'a rustc_mir::Statement<'tcx>) -> Self {
            Self::statement(statement.source_info.span, format!("{statement:?}"))
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_generic_param, code = "FLUX")]
    pub struct UnsupportedGenericParam {
        #[primary_span]
        span: Span,
    }

    impl UnsupportedGenericParam {
        pub fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_type_of, code = "FLUX")]
    pub struct UnsupportedTypeOf<'tcx> {
        #[primary_span]
        span: Span,
        #[note]
        note: (),
        reason: String,
        ty: rustc_middle::ty::Ty<'tcx>,
    }

    impl<'tcx> UnsupportedTypeOf<'tcx> {
        pub fn new(span: Span, ty: rustc_middle::ty::Ty<'tcx>, err: UnsupportedType) -> Self {
            Self { span, note: (), reason: err.reason, ty }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_fn_sig, code = "FLUX")]
    pub struct UnsupportedFnSig {
        #[primary_span]
        pub span: Span,
        pub reason: String,
    }
}
