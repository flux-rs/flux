pub use errors::UnsupportedFnSig;
use flux_common::index::IndexVec;
use flux_errors::{FluxSession, ResultExt};
use itertools::Itertools;
use rustc_const_eval::interpret::ConstValue;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir as rustc_mir,
    ty::{
        self as rustc_ty,
        subst::{GenericArgKind, SubstsRef},
        ParamEnv, TyCtxt,
    },
};

use super::{
    mir::{
        AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, CallSubsts, CastKind, Constant,
        FakeReadCause, Instance, LocalDecl, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        Const, EnumDef, FnSig, GenericArg, GenericParamDef, GenericParamDefKind, Generics, Ty,
        VariantDef,
    },
};
use crate::intern::List;

pub struct LoweringCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    rustc_mir: rustc_mir::Body<'tcx>,
}

pub struct UnsupportedType;

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
        let kind = match &stmt.kind {
            rustc_mir::StatementKind::Assign(box (place, rvalue)) => {
                StatementKind::Assign(
                    self.lower_place(place)?,
                    self.lower_rvalue(rvalue, stmt.source_info)?,
                )
            }
            rustc_mir::StatementKind::SetDiscriminant { place, variant_index } => {
                StatementKind::SetDiscriminant(self.lower_place(place)?, *variant_index)
            }
            rustc_mir::StatementKind::FakeRead(box (cause, place)) => {
                StatementKind::FakeRead(Box::new((
                    self.lower_fake_read_cause(*cause)
                        .ok_or_else(|| errors::UnsupportedStatement::new(stmt))
                        .emit(self.sess)?,
                    self.lower_place(place)?,
                )))
            }
            rustc_mir::StatementKind::Nop
            | rustc_mir::StatementKind::StorageLive(_)
            | rustc_mir::StatementKind::StorageDead(_) => StatementKind::Nop,
            rustc_mir::StatementKind::AscribeUserType(
                box (place, rustc_mir::UserTypeProjection { projs, .. }),
                variance,
            ) if projs.is_empty() => {
                StatementKind::AscribeUserType(self.lower_place(place)?, *variance)
            }
            rustc_mir::StatementKind::Retag(_, _)
            | rustc_mir::StatementKind::Deinit(_)
            | rustc_mir::StatementKind::AscribeUserType(..)
            | rustc_mir::StatementKind::Coverage(_)
            | rustc_mir::StatementKind::Intrinsic(_) => {
                return Err(errors::UnsupportedStatement::new(stmt)).emit(self.sess);
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

    fn lower_instance(
        &self,
        trait_f: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Result<Option<Instance>, UnsupportedType> {
        let param_env = self.tcx.param_env(self.rustc_mir.source.def_id());
        match rustc_middle::ty::Instance::resolve(self.tcx, param_env, trait_f, substs) {
            Ok(Some(instance)) => {
                let impl_f = instance.def_id();
                let inst = if impl_f != trait_f {
                    let substs = lower_substs(self.tcx, instance.substs)?;
                    Some(Instance { impl_f, substs })
                } else {
                    None
                };
                Ok(inst)
            }
            _ => Ok(None),
        }
    }

    fn lower_terminator(
        &self,
        terminator: &rustc_mir::Terminator<'tcx>,
    ) -> Result<Terminator<'tcx>, ErrorGuaranteed> {
        let kind = match &terminator.kind {
            rustc_mir::TerminatorKind::Return => TerminatorKind::Return,
            rustc_mir::TerminatorKind::Call {
                func, args, destination, target, cleanup, ..
            } => {
                let (func, substs) = match func.ty(&self.rustc_mir, self.tcx).kind() {
                    rustc_middle::ty::TyKind::FnDef(fn_def, substs) => {
                        let lowered_substs = lower_substs(self.tcx, substs)
                            .map_err(|_| errors::UnsupportedTerminator::new(terminator))
                            .emit(self.sess)?;
                        (*fn_def, CallSubsts { orig: substs, lowered: lowered_substs })
                    }
                    _ => Err(errors::UnsupportedTerminator::new(terminator)).emit(self.sess)?,
                };

                let destination = self.lower_place(destination)?;

                let instance = self
                    .lower_instance(func, substs.orig)
                    .map_err(|_| errors::UnsupportedTerminator::new(terminator))
                    .emit(self.sess)?;

                TerminatorKind::Call {
                    func,
                    substs,
                    destination,
                    target: *target,
                    args: args
                        .iter()
                        .map(|arg| self.lower_operand(arg))
                        .try_collect()?,
                    cleanup: *cleanup,
                    instance,
                }
            }
            rustc_mir::TerminatorKind::SwitchInt { discr, targets, .. } => {
                TerminatorKind::SwitchInt {
                    discr: self.lower_operand(discr)?,
                    targets: targets.clone(),
                }
            }
            rustc_mir::TerminatorKind::Goto { target } => TerminatorKind::Goto { target: *target },
            rustc_mir::TerminatorKind::Drop { place, target, unwind } => {
                TerminatorKind::Drop {
                    place: self.lower_place(place)?,
                    target: *target,
                    unwind: *unwind,
                }
            }
            rustc_mir::TerminatorKind::DropAndReplace { place, value, target, unwind } => {
                TerminatorKind::DropAndReplace {
                    place: self.lower_place(place)?,
                    value: self.lower_operand(value)?,
                    target: *target,
                    unwind: *unwind,
                }
            }
            rustc_mir::TerminatorKind::Assert { cond, target, expected, msg, .. } => {
                TerminatorKind::Assert {
                    cond: self.lower_operand(cond)?,
                    expected: *expected,
                    target: *target,
                    msg: self
                        .lower_assert_msg(msg)
                        .ok_or_else(|| errors::UnsupportedTerminator::new(terminator))
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
                return Err(errors::UnsupportedTerminator::new(terminator)).emit(self.sess);
            }
        };
        Ok(Terminator { kind, source_info: terminator.source_info })
    }

    fn lower_rvalue(
        &self,
        rvalue: &rustc_mir::Rvalue<'tcx>,
        source_info: rustc_mir::SourceInfo,
    ) -> Result<Rvalue, ErrorGuaranteed> {
        match rvalue {
            rustc_mir::Rvalue::Use(op) => Ok(Rvalue::Use(self.lower_operand(op)?)),
            rustc_mir::Rvalue::BinaryOp(bin_op, operands) => {
                Ok(Rvalue::BinaryOp(
                    self.lower_bin_op(*bin_op)
                        .ok_or_else(|| errors::UnsupportedRvalue::new(source_info.span, rvalue))
                        .emit(self.sess)?,
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
                let aggregate_kind = self
                    .lower_aggregate_kind(aggregate_kind)
                    .ok_or_else(|| errors::UnsupportedRvalue::new(source_info.span, rvalue))
                    .emit(self.sess)?;
                let args = args.iter().map(|op| self.lower_operand(op)).try_collect()?;
                Ok(Rvalue::Aggregate(aggregate_kind, args))
            }
            rustc_mir::Rvalue::Discriminant(p) => Ok(Rvalue::Discriminant(self.lower_place(p)?)),
            rustc_mir::Rvalue::Len(place) => Ok(Rvalue::Len(self.lower_place(place)?)),
            rustc_mir::Rvalue::Cast(kind, op, ty) => {
                let kind = self
                    .lower_cast_kind(*kind)
                    .ok_or_else(|| errors::UnsupportedRvalue::new(source_info.span, rvalue))
                    .emit(self.sess)?;
                let op = self.lower_operand(op)?;
                let ty = lower_ty(self.tcx, *ty)
                    .map_err(|_| errors::UnsupportedRvalue::new(source_info.span, rvalue))
                    .emit(self.sess)?;
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
                Err(errors::UnsupportedRvalue::new(source_info.span, rvalue)).emit(self.sess)
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
    ) -> Option<AggregateKind> {
        match aggregate_kind {
            rustc_mir::AggregateKind::Adt(def_id, variant_idx, substs, None, None) => {
                Some(AggregateKind::Adt(
                    *def_id,
                    *variant_idx,
                    lower_substs(self.tcx, substs).ok()?,
                ))
            }
            rustc_mir::AggregateKind::Array(ty) => {
                Some(AggregateKind::Array(lower_ty(self.tcx, *ty).ok()?))
            }
            rustc_mir::AggregateKind::Tuple => Some(AggregateKind::Tuple),
            rustc_mir::AggregateKind::Adt(..)
            | rustc_mir::AggregateKind::Closure(_, _)
            | rustc_mir::AggregateKind::Generator(_, _, _) => None,
        }
    }

    fn lower_bin_op(&self, bin_op: rustc_mir::BinOp) -> Option<BinOp> {
        match bin_op {
            rustc_mir::BinOp::Add => Some(BinOp::Add),
            rustc_mir::BinOp::Sub => Some(BinOp::Sub),
            rustc_mir::BinOp::Gt => Some(BinOp::Gt),
            rustc_mir::BinOp::Ge => Some(BinOp::Ge),
            rustc_mir::BinOp::Lt => Some(BinOp::Lt),
            rustc_mir::BinOp::Le => Some(BinOp::Le),
            rustc_mir::BinOp::Eq => Some(BinOp::Eq),
            rustc_mir::BinOp::Ne => Some(BinOp::Ne),
            rustc_mir::BinOp::Mul => Some(BinOp::Mul),
            rustc_mir::BinOp::Div => Some(BinOp::Div),
            rustc_mir::BinOp::Rem => Some(BinOp::Rem),
            rustc_mir::BinOp::BitAnd => Some(BinOp::BitAnd),
            rustc_mir::BinOp::BitXor
            | rustc_mir::BinOp::BitOr
            | rustc_mir::BinOp::Shl
            | rustc_mir::BinOp::Shr
            | rustc_mir::BinOp::Offset => None,
        }
    }

    fn lower_operand(&self, op: &rustc_mir::Operand<'tcx>) -> Result<Operand, ErrorGuaranteed> {
        match op {
            rustc_mir::Operand::Copy(place) => Ok(Operand::Copy(self.lower_place(place)?)),
            rustc_mir::Operand::Move(place) => Ok(Operand::Move(self.lower_place(place)?)),
            rustc_mir::Operand::Constant(c) => Ok(Operand::Constant(self.lower_constant(c)?)),
        }
    }

    fn lower_place(&self, place: &rustc_mir::Place<'tcx>) -> Result<Place, ErrorGuaranteed> {
        let mut projection = vec![];
        for elem in place.projection {
            match elem {
                rustc_mir::PlaceElem::Deref => projection.push(PlaceElem::Deref),
                rustc_mir::PlaceElem::Field(field, _) => projection.push(PlaceElem::Field(field)),
                rustc_mir::PlaceElem::Downcast(_, variant_idx) => {
                    projection.push(PlaceElem::Downcast(variant_idx));
                }
                _ => {
                    return Err(self.sess.err(&format!("place not supported: `{place:?}`")));
                }
            }
        }
        Ok(Place { local: place.local, projection })
    }

    fn lower_constant(
        &self,
        constant: &rustc_mir::Constant<'tcx>,
    ) -> Result<Constant, ErrorGuaranteed> {
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
        .ok_or_else(|| errors::UnsupportedConstant::new(constant))
        .emit(self.sess)
    }

    fn lower_assert_msg(&self, msg: &rustc_mir::AssertMessage) -> Option<&'static str> {
        use rustc_mir::AssertKind::*;
        match msg {
            DivisionByZero(_) => Some("possible division by zero"),
            RemainderByZero(_) => Some("possible remainder with a divisor of zero"),
            Overflow(rustc_mir::BinOp::Div, _, _) => Some("possible division with overflow"),
            Overflow(rustc_mir::BinOp::Rem, _, _) => Some("possible remainder with overflow"),
            BoundsCheck { .. } => Some("index out of bounds"),
            _ => None,
        }
    }
}

/// [NOTE:Fake Predecessors] The `FalseEdge/imaginary_target` edges mess up
/// the "is_join_point" computation which creates spurious join points that
/// lose information e.g. in match arms, the k+1-th arm has the k-th arm as
/// a "fake" predecessor so we lose the assumptions specific to the k+1-th
/// arm due to a spurious join. This code corrects for this problem by
/// computing the number of "fake" predecessors and decreasing them from
/// the total number of "predecessors" returned by `rustc`.
/// The option is to recompute "predecessors" from scratch but we may miss
/// some cases there. (see also `is_join_point`)

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
    lower_ty(tcx, tcx.type_of(def_id))
        .map_err(|_| errors::UnsupportedTypeOf::new(span))
        .emit(sess)
}

pub fn lower_enum_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    sess: &FluxSession,
    adt_def: rustc_ty::AdtDef<'tcx>,
) -> Result<EnumDef, ErrorGuaranteed> {
    let adt_def_id = adt_def.did();
    let mut variants = vec![];
    for variant_def in adt_def.variants().into_iter() {
        variants.push(lower_variant_def(tcx, sess, adt_def_id, variant_def)?)
    }
    Ok(EnumDef { variants })
}

pub fn lower_variant_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    adt_def_id: DefId,
    variant_def: &rustc_ty::VariantDef,
) -> Result<VariantDef, ErrorGuaranteed> {
    let fields = variant_def
        .fields
        .iter()
        .map(|field| lower_type_of(tcx, sess, field.did))
        .collect_vec();
    let fields: Result<Vec<Ty>, ErrorGuaranteed> = fields.into_iter().collect();
    let fields = List::from_vec(fields?);
    let ret = lower_type_of(tcx, sess, adt_def_id)?;
    Ok(VariantDef { fields, ret })
}

pub fn lower_fn_sig_of(tcx: TyCtxt, def_id: DefId) -> Result<FnSig, errors::UnsupportedFnSig> {
    let fn_sig = tcx.fn_sig(def_id);
    let span = tcx.def_span(def_id);
    lower_fn_sig(tcx, fn_sig).map_err(|_| errors::UnsupportedFnSig { span })
}

fn lower_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_sig: rustc_ty::PolyFnSig<'tcx>,
) -> Result<FnSig, UnsupportedType> {
    let fn_sig = tcx.erase_late_bound_regions(fn_sig);
    let inputs_and_output = List::from_vec(
        fn_sig
            .inputs_and_output
            .iter()
            .map(|ty| lower_ty(tcx, ty))
            .try_collect()?,
    );
    Ok(FnSig { inputs_and_output })
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
        rustc_ty::Array(ty, _) => Ok(Ty::mk_array(lower_ty(tcx, *ty)?, Const)),
        rustc_ty::Slice(ty) => Ok(Ty::mk_slice(lower_ty(tcx, *ty)?)),
        _ => Err(UnsupportedType),
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
        GenericArgKind::Const(_) | GenericArgKind::Lifetime(_) => Err(UnsupportedType),
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
        _ => {
            return Err(errors::UnsupportedGenericParam::new(tcx.def_span(generic.def_id)))
                .emit(sess)
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
    #[diag(lowering::unsupported_statement, code = "FLUX")]
    pub struct UnsupportedStatement {
        #[primary_span]
        pub span: Span,
        pub statement: String,
    }

    impl UnsupportedStatement {
        pub fn new(statement: &rustc_mir::Statement) -> Self {
            Self { span: statement.source_info.span, statement: format!("{statement:?}") }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_terminator, code = "FLUX")]
    pub struct UnsupportedTerminator {
        #[primary_span]
        #[label]
        span: Span,
        terminator: String,
    }

    impl UnsupportedTerminator {
        pub fn new(terminator: &rustc_mir::Terminator) -> Self {
            Self { span: terminator.source_info.span, terminator: format!("{terminator:?}") }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_rvalue, code = "FLUX")]
    pub struct UnsupportedRvalue {
        #[primary_span]
        #[label]
        span: Span,
        rvalue: String,
    }

    impl UnsupportedRvalue {
        pub fn new(span: Span, rvalue: &rustc_mir::Rvalue) -> Self {
            Self { span, rvalue: format!("{rvalue:?}") }
        }
    }
    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_constant, code = "FLUX")]
    pub struct UnsupportedConstant {
        #[primary_span]
        #[label]
        span: Span,
        constant: String,
    }

    impl UnsupportedConstant {
        pub fn new(constant: &rustc_mir::Constant) -> Self {
            Self { span: constant.span, constant: format!("{constant:?}") }
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
    pub struct UnsupportedTypeOf {
        #[primary_span]
        span: Span,
    }

    impl UnsupportedTypeOf {
        pub fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(lowering::unsupported_fn_sig, code = "FLUX")]
    pub struct UnsupportedFnSig {
        #[primary_span]
        pub span: Span,
    }
}
