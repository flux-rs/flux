use flux_common::index::IndexVec;
use itertools::Itertools;
use rustc_const_eval::interpret::ConstValue;
use rustc_errors::{DiagnosticId, ErrorGuaranteed};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    middle::resolve_lifetime::Set1,
    mir as rustc_mir,
    ty::{
        self as rustc_ty,
        subst::{GenericArgKind, SubstsRef},
        ParamEnv, TyCtxt,
    },
};
use rustc_span::Span;

use super::{
    mir::{
        AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, CallSubsts, Constant,
        FakeReadCause, Instance, LocalDecl, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{
        Const, ConstKind, EnumDef, FnSig, GenericArg, GenericParamDef, GenericParamDefKind,
        Generics, Ty, ValTree, VariantDef,
    },
};
use crate::intern::List;

pub struct LoweringCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    rustc_mir: rustc_mir::Body<'tcx>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    pub fn lower_mir_body(
        tcx: TyCtxt<'tcx>,
        rustc_mir: rustc_mir::Body<'tcx>,
    ) -> Result<Body<'tcx>, ErrorGuaranteed> {
        let lower = Self { tcx, rustc_mir };

        let basic_blocks = lower
            .rustc_mir
            .basic_blocks()
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
            ty: lower_ty(self.tcx, local_decl.ty)?,
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
                    self.lower_fake_read_cause(*cause)?,
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
            | rustc_mir::StatementKind::CopyNonOverlapping(_) => {
                return self.emit_err(
                    Some(stmt.source_info.span),
                    format!("unsupported statement: `{stmt:?}`"),
                );
            }
        };
        Ok(Statement { kind, source_info: stmt.source_info })
    }

    fn lower_fake_read_cause(
        &self,
        cause: rustc_mir::FakeReadCause,
    ) -> Result<FakeReadCause, ErrorGuaranteed> {
        match cause {
            rustc_mir::FakeReadCause::ForLet(def_id) => Ok(FakeReadCause::ForLet(def_id)),
            rustc_mir::FakeReadCause::ForMatchedPlace(def_id) => {
                Ok(FakeReadCause::ForMatchedPlace(def_id))
            }
            rustc_mir::FakeReadCause::ForMatchGuard
            | rustc_mir::FakeReadCause::ForGuardBinding
            | rustc_mir::FakeReadCause::ForIndex { .. } => {
                self.emit_err(None, format!("unsupported fake read cause: `{:?}`", cause))
            }
        }
    }

    fn lower_instance(
        &self,
        trait_f: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Result<Option<Instance>, ErrorGuaranteed> {
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
                        let lowered_substs = lower_substs(self.tcx, substs)?;
                        (*fn_def, CallSubsts { orig: substs, lowered: lowered_substs })
                    }
                    _ => {
                        return self.emit_err(
                            Some(terminator.source_info.span),
                            "unsupported function call",
                        );
                    }
                };

                let destination = self.lower_place(destination)?;

                let instance = self.lower_instance(func, substs.orig)?;

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
                    msg: self.lower_assert_msg(msg)?,
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
                return self.emit_err(
                    Some(terminator.source_info.span),
                    format!("unsupported terminator kind: {:?}", terminator.kind),
                );
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
            rustc_mir::Rvalue::Repeat(_, _)
            | rustc_mir::Rvalue::Ref(_, _, _)
            | rustc_mir::Rvalue::ThreadLocalRef(_)
            | rustc_mir::Rvalue::AddressOf(_, _)
            | rustc_mir::Rvalue::Cast(_, _, _)
            | rustc_mir::Rvalue::CheckedBinaryOp(_, _)
            | rustc_mir::Rvalue::NullaryOp(_, _)
            | rustc_mir::Rvalue::CopyForDeref(_)
            | rustc_mir::Rvalue::ShallowInitBox(_, _) => {
                self.emit_err(Some(source_info.span), format!("unsupported rvalue: `{rvalue:?}`"))
            }
        }
    }

    fn lower_aggregate_kind(
        &self,
        aggregate_kind: &rustc_mir::AggregateKind<'tcx>,
    ) -> Result<AggregateKind, ErrorGuaranteed> {
        match aggregate_kind {
            rustc_mir::AggregateKind::Adt(def_id, variant_idx, substs, None, None) => {
                Ok(AggregateKind::Adt(*def_id, *variant_idx, lower_substs(self.tcx, substs)?))
            }
            rustc_mir::AggregateKind::Array(ty) => {
                Ok(AggregateKind::Array(lower_ty(self.tcx, *ty)?))
            }
            rustc_mir::AggregateKind::Adt(..)
            | rustc_mir::AggregateKind::Tuple
            | rustc_mir::AggregateKind::Closure(_, _)
            | rustc_mir::AggregateKind::Generator(_, _, _) => {
                self.emit_err(None, format!("unsupported aggregate kind: `{:?}`", aggregate_kind))
            }
        }
    }

    fn lower_bin_op(&self, bin_op: rustc_mir::BinOp) -> Result<BinOp, ErrorGuaranteed> {
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
            | rustc_mir::BinOp::Offset => {
                self.emit_err(None, format!("unsupported binary operation: `{bin_op:?}`"))
            }
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
                    return Err(self
                        .tcx
                        .sess
                        .err(&format!("place not supported: `{place:?}`")));
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
        let span = constant.span;

        match (&constant.literal, constant.ty().kind()) {
            (ConstantKind::Val(ConstValue::Scalar(Scalar::Int(scalar)), ty), _) => {
                scalar_int_to_constant(tcx, *scalar, *ty)
            }
            (ConstantKind::Val(ConstValue::Slice { .. }, _), TyKind::Ref(_, ref_ty, _))
                if ref_ty.is_str() =>
            {
                Some(Constant::Str)
            }
            (ConstantKind::Ty(c), _) => {
                // HACK(nilehmann) we evaluate the constant to support u32::MAX
                // we should instead lower it as is and refine its type.
                let c = c.eval(tcx, ParamEnv::empty());
                if let rustc_ty::ConstKind::Value(rustc_ty::ValTree::Leaf(scalar)) = c.kind() {
                    scalar_int_to_constant(tcx, scalar, c.ty())
                } else {
                    None
                }
            }
            (_, TyKind::Tuple(tys)) if tys.is_empty() => return Ok(Constant::Unit),
            _ => None,
        }
        .ok_or_else(|| {
            emit_err(self.tcx, Some(span), format!("constant not supported: `{constant:?}`"))
        })
    }

    fn lower_assert_msg(
        &self,
        msg: &rustc_mir::AssertMessage,
    ) -> Result<&'static str, ErrorGuaranteed> {
        use rustc_mir::AssertKind::*;
        match msg {
            DivisionByZero(_) => Ok("possible division by zero"),
            RemainderByZero(_) => Ok("possible remainder with a divisor of zero"),
            Overflow(rustc_mir::BinOp::Div, _, _) => Ok("possible division with overflow"),
            Overflow(rustc_mir::BinOp::Rem, _, _) => Ok("possible remainder with overflow"),
            BoundsCheck { .. } => Ok("index out of bounds"),
            _ => self.emit_err(None, format!("unsupported assert message: `{msg:?}`")),
        }
    }

    fn emit_err<S: AsRef<str>, T>(&self, span: Option<Span>, msg: S) -> Result<T, ErrorGuaranteed> {
        Err(emit_err(self.tcx, span, msg))
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

fn lower_type_of(tcx: TyCtxt, def_id: DefId) -> Result<Ty, ErrorGuaranteed> {
    lower_ty(tcx, tcx.type_of(def_id))
}

pub fn lower_enum_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: rustc_ty::AdtDef<'tcx>,
) -> Result<EnumDef, ErrorGuaranteed> {
    let adt_def_id = adt_def.did();
    let mut variants = vec![];
    for variant_def in adt_def.variants().into_iter() {
        variants.push(lower_variant_def(tcx, adt_def_id, variant_def)?)
    }
    Ok(EnumDef { variants })
}

pub fn lower_variant_def(
    tcx: TyCtxt,
    adt_def_id: DefId,
    variant_def: &rustc_ty::VariantDef,
) -> Result<VariantDef, ErrorGuaranteed> {
    let fields = variant_def
        .fields
        .iter()
        .map(|field| lower_type_of(tcx, field.did))
        .collect_vec();
    let fields: Result<Vec<Ty>, ErrorGuaranteed> = fields.into_iter().collect();
    let fields = List::from_vec(fields?);
    let ret = lower_type_of(tcx, adt_def_id)?;
    Ok(VariantDef { fields, ret })
}

pub fn lower_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_sig: rustc_ty::PolyFnSig<'tcx>,
) -> Result<FnSig, ErrorGuaranteed> {
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

pub fn lower_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_ty::Ty<'tcx>) -> Result<Ty, ErrorGuaranteed> {
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
        rustc_ty::Tuple(tys) if tys.is_empty() => Ok(Ty::mk_tuple(vec![])),
        rustc_ty::Array(ty, c) => Ok(Ty::mk_array(lower_ty(tcx, *ty)?, lower_const(tcx, *c)?)),
        _ => {
            Err(emit_err(tcx, None, format!("unsupported type `{ty:?}`, kind: `{:?}`", ty.kind())))
        }
    }
}

fn lower_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: rustc_ty::Const<'tcx>,
) -> Result<Const, ErrorGuaranteed> {
    let kind = match c.kind() {
        rustc_ty::ConstKind::Value(val) => ConstKind::Value(lower_valtree(tcx, val)?),
        rustc_ty::ConstKind::Param(_)
        | rustc_ty::ConstKind::Infer(_)
        | rustc_ty::ConstKind::Bound(_, _)
        | rustc_ty::ConstKind::Placeholder(_)
        | rustc_ty::ConstKind::Unevaluated(_)
        | rustc_ty::ConstKind::Error(_) => {
            return Err(emit_err(tcx, None, format!("unsupported const `{c:?}`")));
        }
    };
    Ok(Const { ty: lower_ty(tcx, c.ty())?, kind })
}

fn lower_valtree(tcx: TyCtxt, val: rustc_ty::ValTree) -> Result<ValTree, ErrorGuaranteed> {
    match val {
        rustc_ty::ValTree::Leaf(scalar) => Ok(ValTree::Leaf(scalar)),
        rustc_ty::ValTree::Branch(_) => {
            Err(emit_err(tcx, None, format!("unsupported valtree {val:?}")))
        }
    }
}

fn lower_substs<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<List<GenericArg>, ErrorGuaranteed> {
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
) -> Result<GenericArg, ErrorGuaranteed> {
    match arg.unpack() {
        GenericArgKind::Type(ty) => Ok(GenericArg::Ty(lower_ty(tcx, ty)?)),
        GenericArgKind::Const(_) | GenericArgKind::Lifetime(_) => {
            Err(emit_err(tcx, None, format!("unsupported generic argument: `{arg:?}`")))
        }
    }
}

pub fn lower_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    generics: &'tcx rustc_ty::Generics,
) -> Result<Generics<'tcx>, ErrorGuaranteed> {
    let params = List::from_vec(
        generics
            .params
            .iter()
            .map(|generic| lower_generic_param_def(tcx, generic))
            .try_collect()?,
    );
    Ok(Generics { params, rustc: generics })
}

fn lower_generic_param_def(
    tcx: TyCtxt,
    generic: &rustc_ty::GenericParamDef,
) -> Result<GenericParamDef, ErrorGuaranteed> {
    let kind = match generic.kind {
        rustc_ty::GenericParamDefKind::Type {
            has_default,
            object_lifetime_default: Set1::Empty,
            synthetic: false,
        } => GenericParamDefKind::Type { has_default },
        _ => {
            return Err(emit_err(
                tcx,
                None,
                format!("unsupported generic parameter: `{generic:?}`"),
            ))
        }
    };
    Ok(GenericParamDef { def_id: generic.def_id, kind })
}

fn emit_err<S: AsRef<str>>(tcx: TyCtxt, span: Option<Span>, msg: S) -> ErrorGuaranteed {
    let mut diagnostic = tcx
        .sess
        .struct_err_with_code(msg.as_ref(), DiagnosticId::Error("flux".to_string()));
    if let Some(span) = span {
        diagnostic.set_span(span);
    }
    diagnostic.emit()
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
