//! Handles the translation from Rust MIR to the CPS IR.

use std::{collections::HashMap, iter::FromIterator};

use dataflow::ResultsCursor;
use liquid_rust_core::{ast::*, names::*};
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_index::vec::Idx;
use rustc_middle::{
    mir::{
        self,
        interpret::{ConstValue, Scalar},
        terminator::TerminatorKind,
        PlaceRef,
    },
    ty::{self, ParamEnv},
};
use rustc_mir::dataflow::{
    self,
    impls::MaybeUninitializedPlaces,
    move_paths::{LookupResult, MoveData},
    Analysis, MoveDataParamEnv,
};
use rustc_target::abi;

// TODO: This is ugly as hell, but the MoveDataParamEnv struct fields
// are private, and we want to reuse the MIR dataflow analysis
// that the compiler provides us
struct MPDE<'tcx> {
    pub move_data: MoveData<'tcx>,
    pub param_env: ParamEnv<'tcx>,
}

fn create_mpde<'tcx>(
    move_data: MoveData<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> MoveDataParamEnv<'tcx> {
    let res = MPDE {
        move_data,
        param_env,
    };

    unsafe { std::mem::transmute::<MPDE<'tcx>, MoveDataParamEnv<'tcx>>(res) }
}

fn translate_statement(stmt: &mir::Statement) -> Statement<()> {
    match &stmt.kind {
        mir::StatementKind::Assign(pr) => {
            let place = translate_place(&pr.0);
            let rval = translate_rvalue(&pr.1);

            Statement {
                kind: StatementKind::Assign(place, rval),
                source_info: (),
            }
        }
        mir::StatementKind::StorageDead(..)
        | mir::StatementKind::StorageLive(..)
        | mir::StatementKind::Nop => Statement {
            kind: StatementKind::Nop,
            source_info: (),
        },
        _ => todo!(),
    }
}

/// Translates an `mir::Place` to a CPS IR Place.
fn translate_place(from: &mir::Place) -> Place {
    let base = Local::new(from.local.as_usize());
    let mut projs = vec![];

    for proj in from.projection {
        match proj {
            mir::ProjectionElem::Field(f, _ty) => projs.push(Proj::Field(f.as_usize())),
            mir::ProjectionElem::Deref => projs.push(Proj::Deref),
            _ => todo!(),
        };
    }

    Place { base, projs }
}

fn translate_op(from: &mir::Operand) -> Operand {
    match from {
        mir::Operand::Copy(p) => Operand::Copy(translate_place(p)),
        mir::Operand::Move(p) => Operand::Move(translate_place(p)),
        mir::Operand::Constant(bc) => translate_const(bc),
    }
}

// Adapted from
// https://github.com/rust-lang/rust/blob/master/compiler/rustc_middle/src/ty/print/pretty.rs
fn translate_const(from: &mir::Constant) -> Operand {
    match from.literal.val {
        ty::ConstKind::Value(ConstValue::Scalar(s)) => {
            match (s, from.literal.ty.kind()) {
                // Unit
                (Scalar::Int(s), _) if s.size() == abi::Size::ZERO => {
                    Operand::Constant(Constant::Unit)
                }
                // Bool
                (Scalar::Int(s), ty::Bool) if s == ty::ScalarInt::FALSE => {
                    Operand::Constant(Constant::Bool(false))
                }
                (Scalar::Int(s), ty::Bool) if s == ty::ScalarInt::TRUE => {
                    Operand::Constant(Constant::Bool(true))
                }
                // TODO: Floats, when support is added
                // Int
                (Scalar::Int(s), ty::Uint(_) | ty::Int(_)) => {
                    Operand::Constant(Constant::Int(s.to_bits(s.size()).unwrap()))
                }
                // TODO: Signed ints, when support is added
                // TODO: Chars, when support is added
                _ => todo!("{:?}", from),
            }
        }
        _ => todo!(),
    }
}

fn translate_rvalue(from: &mir::Rvalue) -> Rvalue {
    match from {
        mir::Rvalue::Use(op) => Rvalue::Use(translate_op(op)),
        mir::Rvalue::BinaryOp(bin_op, op1, op2) => Rvalue::BinaryOp(
            translate_bin_op(*bin_op),
            translate_op(op1),
            translate_op(op2),
        ),
        mir::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => Rvalue::CheckedBinaryOp(
            translate_bin_op(*bin_op),
            translate_op(op1),
            translate_op(op2),
        ),
        mir::Rvalue::Ref(_, bk, place) => {
            let bk = match bk {
                mir::BorrowKind::Mut { .. } => BorrowKind::Mut,
                mir::BorrowKind::Shared => BorrowKind::Shared,
                _ => todo!(),
            };
            Rvalue::Ref(bk, translate_place(place))
        }
        mir::Rvalue::UnaryOp(un_op, op) => {
            Rvalue::UnaryOp(translate_un_op(*un_op), translate_op(op))
        }
        _ => todo!(),
    }
}

fn translate_bin_op(bin_op: mir::BinOp) -> BinOp {
    match bin_op {
        mir::BinOp::Add => BinOp::Add,
        mir::BinOp::Sub => BinOp::Sub,
        mir::BinOp::Lt => BinOp::Lt,
        mir::BinOp::Le => BinOp::Le,
        mir::BinOp::Eq => BinOp::Eq,
        mir::BinOp::Ge => BinOp::Ge,
        mir::BinOp::Gt => BinOp::Gt,
        _ => todo!(),
    }
}

fn translate_un_op(un_op: mir::UnOp) -> UnOp {
    match un_op {
        mir::UnOp::Not => UnOp::Not,
        mir::UnOp::Neg => UnOp::Neg,
    }
}

fn get_base_ty(t: ty::Ty) -> BaseTy {
    match t.kind() {
        ty::TyKind::Bool => BaseTy::Bool,
        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => BaseTy::Int,
        _ => todo!(),
    }
}

/// Creates a `TypeLayout` based on a Rust `TyKind`.
fn get_layout(t: ty::Ty) -> TypeLayout {
    // Get the Rust type for ints, bools, tuples (of ints, bools, tuples)
    // Do case analysis, generate TypeLayout based on that.
    // Give up if not supported type
    // match &t.kind {
    //     ty::TyKind::Bool => TypeLayout::Block(size_of::<bool>().try_into().unwrap()),
    //     ty::TyKind::Int(it) => TypeLayout::Block(
    //         it.bit_width()
    //             .map(|x| x >> 3)
    //             .unwrap_or_else(|| size_of::<isize>().try_into().unwrap()) as u32,
    //     ),
    //     ty::TyKind::Uint(it) => TypeLayout::Block(
    //         it.bit_width()
    //             .map(|x| x >> 3 as u32)
    //             .unwrap_or_else(|| size_of::<isize>().try_into().unwrap()) as u32,
    //     ),
    //     ty::TyKind::Tuple(_) => {
    //         TypeLayout::Tuple(t.tuple_fields().map(|c| get_layout(c)).collect::<Vec<_>>())
    //     }
    //     _ => todo!(),
    // }
    match t.kind() {
        ty::TyKind::Tuple(_) => {
            tuple_layout_or_block(t.tuple_fields().map(|c| get_layout(c)).collect())
        }
        _ => TypeLayout::Block(1),
    }
}

// Transformer state struct should include a mapping from locals to refinements too

pub struct Transformer<'low, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    annots: &'low mut HashMap<DefId, FnDecl>,
    body: &'low mir::Body<'tcx>,
    move_data: MoveData<'tcx>,
    maybe_uninitialized_cursor: ResultsCursor<'low, 'tcx, MaybeUninitializedPlaces<'low, 'tcx>>,
    names: NameProducer,
}

impl<'low, 'tcx> Transformer<'low, 'tcx> {
    pub fn translate(
        tcx: ty::TyCtxt<'tcx>,
        annots: &mut HashMap<DefId, FnDecl>,
        body: &mir::Body<'tcx>,
    ) -> FnDef<()> {
        let param_env = tcx.param_env(body.source.def_id());
        let mdpe_move_data = MoveData::gather_moves(body, tcx, param_env).unwrap_or_else(|x| x.0);
        let move_data = MoveData::gather_moves(body, tcx, param_env).unwrap_or_else(|x| x.0);
        let mdpe = create_mpde(mdpe_move_data, param_env);

        let maybe_uninitialized_cursor = MaybeUninitializedPlaces::new(tcx, body, &mdpe)
            .into_engine(tcx, body)
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        let mut transformer = Transformer {
            tcx,
            annots,
            body,
            maybe_uninitialized_cursor,
            move_data,
            names: NameProducer::new(body),
        };
        transformer.translate_body()
    }

    /// Generates a fresh variable with a certain prefix.
    fn fresh_local(&mut self) -> Local {
        self.names.fresh_local()
    }

    fn fresh_location(&mut self) -> Location {
        self.names.fresh_location()
    }

    /// Returns a `Ty` where all the refinements should be inferred
    fn get_holy_type(&mut self, t: ty::Ty<'tcx>) -> Ty {
        match t.kind() {
            ty::TyKind::Tuple(substs) if !substs.is_empty() => Ty::Tuple(
                t.tuple_fields()
                    .enumerate()
                    .map(|(i, f)| (Field::new(i), self.get_holy_type(f)))
                    .collect(),
            ),
            ty::TyKind::Tuple(_) => Ty::unit(),
            _ => Ty::Refine(get_base_ty(t), Refine::Infer),
        }
    }

    /// Translates an MIR function body to a CPS IR `FnDef`.
    pub fn translate_body(&mut self) -> FnDef<()> {
        // We then generate a jump instruction to jump to the continuation
        // corresponding to the first/root basic block, bb0.
        let mut nb = FnBody::Jump {
            target: ContId::new(0),
            args: Vec::new(),
        };

        // Translate every basic block into a continuation definition and define them all
        // to be mutually recursive.
        nb = FnBody::LetCont(
            self.body
                .basic_blocks()
                .indices()
                .map(|bb| self.translate_basic_block(bb))
                .collect(),
            box nb,
        );

        // We finish by taking care of the let bindings - let binding all of the
        // locals in our MIR function body.
        // We do this because a FnBody::Sequence takes a statement and the rest
        // of the function body; we do this at the end so that we have a "rest of`
        // the function body"
        for (ix, decl) in self.body.local_decls.iter_enumerated().rev() {
            if (1..=self.body.arg_count).contains(&ix.index()) {
                // Skip over argument locals, they're printed in the signature.
                continue;
            }

            let sym = Local::new(ix.as_usize());
            let s = Statement {
                kind: StatementKind::Let(sym, get_layout(decl.ty)),
                source_info: (),
            };
            nb = FnBody::Seq(s, Box::new(nb));
        }

        // For our function type, if we have a provided function type annotation,
        // we use that. Otherwise, we fall back to generating holy types etc.
        if let Some(ty) = self.annots.remove(&self.body.source.def_id()) {
            let mut params = vec![];

            for lix in self.body.args_iter() {
                let arg = Local::new(lix.index());

                params.push(arg);
            }

            // TODO: Different out_heap than input heap?
            FnDef {
                // name: Symbol::intern(self.tcx.def_path_str(source.def_id()).as_str()),
                ty,
                params,
                ret: self.retk(),
                body: nb,
            }
        } else {
            let mut inputs = vec![];
            let mut params = vec![];
            let mut in_heap = vec![];

            for lix in self.body.args_iter() {
                let decl = &self.body.local_decls[lix];

                let arg = Local::new(lix.index());
                let loc = self.fresh_location();
                let ty = self.get_holy_type(decl.ty);

                params.push(arg);
                inputs.push((arg, loc));
                in_heap.push((loc, ty));
            }

            // Our return type is local _0; we want to get a holy type here as
            // our return type
            let mut out_heap = vec![];
            let output = self.fresh_location();
            let out_ty = self.get_holy_type(self.body.return_ty());
            out_heap.push((output, out_ty));

            // TODO: regions, outputs
            let regions = vec![];
            let outputs = vec![];

            let fn_ty = FnDecl {
                regions,
                in_heap: Heap::from_iter(in_heap),
                inputs,
                out_heap: Heap::from_iter(out_heap),
                outputs,
                output,
            };

            // TODO: Different out_heap than input heap?
            FnDef {
                // name: Symbol::intern(self.tcx.def_path_str(source.def_id()).as_str()),
                ty: fn_ty,
                params,
                ret: self.retk(),
                body: nb,
            }
        }
    }

    fn translate_basic_block(&mut self, bb: mir::BasicBlock) -> ContDef<()> {
        let bbd = &self.body.basic_blocks()[bb];

        // We generate a statement for the terminator first, then we go through the statements
        // in reverse, building onto the FnBody this way.
        let mut bbod = self.translate_terminator(&bbd.terminator());

        for stmt in bbd.statements.iter().rev() {
            bbod = FnBody::Seq(translate_statement(stmt), box bbod);
        }

        // We update our body here

        // For our continuations, we use all of the locals
        // as our env arguments, keeping the parameters empty.
        // These env arguments point to locations on the heap, one for each
        // env arg. If we know the local to be initialized for sure upon
        // entering this basic block, we give the location a refinement type,
        // where the BasicType corresponds to the type of the local,
        // and the refinement is a hole (we use RefineHole)
        // Otherwise, the heap argument is given an Uninit type, since all types
        // are subtypes of the Uninit type of the same size.

        self.maybe_uninitialized_cursor.seek_to_block_start(bb);

        let mut locals = vec![];
        let mut heap = vec![];

        for (mir_local, decl) in self.body.local_decls.iter_enumerated() {
            let ty = self
                .type_lower_ctxt(mir_local, &mut heap)
                .lower(decl.ty, &mut vec![]);
            let local = Local::new(mir_local.index());
            let l = self.fresh_location();

            locals.push((local, l));
            heap.push((l, ty));
        }

        let cont_ty = ContTy {
            heap: Heap::from_iter(heap),
            locals,
            inputs: vec![],
        };

        ContDef {
            name: ContId::new(bb.as_usize()),
            ty: cont_ty,
            params: vec![],
            body: box bbod,
        }
    }

    #[allow(clippy::clippy::too_many_lines)]
    fn translate_terminator(&mut self, terminator: &mir::Terminator<'tcx>) -> FnBody<()> {
        match &terminator.kind {
            TerminatorKind::Goto { target } => FnBody::Jump {
                target: ContId::new(target.index()),
                args: Vec::new(),
            },
            // TODO: Actually do the asserting
            TerminatorKind::Assert { target, .. } => FnBody::Jump {
                target: ContId::new(target.index()),
                args: Vec::new(),
            },
            TerminatorKind::SwitchInt {
                discr,
                targets,
                switch_ty,
            } => {
                // We have to test our operand against each provided target value.
                // This will turn into nested conditionals: if {} else { if ... }

                // We first start with the else branch, since that's at the leaf of our
                // if-else-if-else chain, and build backwards from there.
                let mut ite = FnBody::Jump {
                    target: ContId::new(targets.otherwise().index()),
                    args: vec![],
                };

                // Then for each value remaining, we create a new FnBody::Ite, jumping to
                // the specified target.
                // We need to collect it because SwitchTargetsIter doesn't implment
                // DoubleEndedIterator
                let targets: Vec<_> = targets.iter().collect();
                for (val, target) in targets.into_iter().rev() {
                    // We first have to translate our discriminator into an AST Operand.
                    let op = translate_op(discr);

                    let then = FnBody::Jump {
                        target: ContId::new(target.index()),
                        args: vec![],
                    };

                    // We can only have places for guards, so we have
                    // to create a place first.
                    let temp = self.fresh_local();
                    // Bools are guaranteed to be one byte, so assuming a one byte
                    // TypeLayout should be ok!
                    let bind = Statement {
                        kind: StatementKind::Let(temp, TypeLayout::Block(1)),
                        source_info: (),
                    };

                    let temp = Place::from(temp);

                    // If the discr type is a bool, we compare to a bool constant.
                    // otherwise, compare with an int constant.
                    let asgn = {
                        let kind = StatementKind::Assign(
                            temp.clone(),
                            if !switch_ty.is_bool() {
                                Rvalue::BinaryOp(
                                    BinOp::Eq,
                                    op,
                                    Operand::Constant(Constant::Int(val)),
                                )
                            } else if val == 0 {
                                Rvalue::UnaryOp(UnOp::Not, op)
                            } else {
                                Rvalue::Use(op)
                            },
                        );
                        Statement {
                            kind,
                            source_info: (),
                        }
                    };

                    ite = FnBody::Seq(
                        bind,
                        Box::new(FnBody::Seq(
                            asgn,
                            Box::new(FnBody::Ite {
                                discr: temp,
                                then: box then,
                                else_: box ite,
                            }),
                        )),
                    );
                }

                // Finally, return the ite.
                ite
            }
            // For returning, we call the return continuation on _0, the let-bound local representing
            // the return value
            TerminatorKind::Return => FnBody::Jump {
                target: self.retk(),
                args: vec![Transformer::retv()],
            },
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let args_temp: Vec<Local> = (0..args.len()).map(|_| self.fresh_local()).collect();

                let mut fb = match func {
                    mir::Operand::Constant(bc) => {
                        let c = &*bc;
                        let kind = c.literal.ty.kind();

                        match kind {
                            ty::TyKind::FnDef(def_id, _) => {
                                let def_id = def_id
                                    .as_local()
                                    .expect("Calls to non-local function are not supported yet.");

                                FnBody::Call {
                                    func: FnId::new(def_id.index()),
                                    args: args_temp.clone(),
                                    destination: destination.map(|(place, bb)| {
                                        (translate_place(&place), ContId::new(bb.as_usize()))
                                    }),
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => todo!(),
                };

                // We now have to actually create and assign locals for our operands.
                for (&temp, arg) in args_temp.iter().zip(args) {
                    // We let-define a new variable for our function arg, then
                    // assign it to the value of the arg.

                    let tys = arg.ty(self.body, self.tcx);
                    let bind = Statement {
                        kind: StatementKind::Let(temp, get_layout(&tys)),
                        source_info: (),
                    };

                    let temp = Place::from(temp);
                    let assign = Statement {
                        kind: StatementKind::Assign(temp, Rvalue::Use(translate_op(arg))),
                        source_info: (),
                    };
                    fb = FnBody::Seq(bind, Box::new(FnBody::Seq(assign, Box::new(fb))));
                }

                fb
            }
            TerminatorKind::Abort => FnBody::Abort,
            _ => todo!(),
        }
    }

    fn type_lower_ctxt<'a>(
        &'a mut self,
        local: mir::Local,
        heap: &'a mut Vec<(Location, Ty)>,
    ) -> TyLowerCtxt<'a, 'low, 'tcx> {
        TyLowerCtxt {
            local,
            names: &mut self.names,
            heap,
            move_data: &self.move_data,
            maybe_uninitialized_cursor: &self.maybe_uninitialized_cursor,
        }
    }

    fn retk(&self) -> ContId {
        ContId::new(self.body.basic_blocks().len())
    }

    fn retv() -> Local {
        Local::new(0)
    }
}

fn tuple_layout_or_block(tup: Vec<TypeLayout>) -> TypeLayout {
    if tup.is_empty() {
        TypeLayout::Block(1)
    } else {
        TypeLayout::Tuple(tup)
    }
}

struct TyLowerCtxt<'a, 'low, 'tcx> {
    local: mir::Local,
    names: &'a mut NameProducer,
    heap: &'a mut Vec<(Location, Ty)>,
    move_data: &'a MoveData<'tcx>,
    maybe_uninitialized_cursor: &'a ResultsCursor<'low, 'tcx, MaybeUninitializedPlaces<'low, 'tcx>>,
}

impl<'a, 'low, 'tcx> TyLowerCtxt<'a, 'low, 'tcx> {
    fn lower(&mut self, ty: ty::Ty<'tcx>, projection: &mut Vec<mir::PlaceElem<'tcx>>) -> Ty {
        if self.is_maybe_unitialized(projection) {
            return self.lower_uninitialized(ty);
        }

        match ty.kind() {
            ty::TyKind::Tuple(subst) if !subst.is_empty() => {
                let tup = ty
                    .tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| {
                        projection.push(mir::PlaceElem::Field(mir::Field::from_usize(i), ty));
                        let r = (Field::new(i), self.lower(ty, projection));
                        projection.pop();
                        r
                    })
                    .collect();
                Ty::Tuple(tup)
            }
            ty::TyKind::Tuple(_) => Ty::unit(),
            ty::TyKind::Bool => Ty::Refine(BaseTy::Bool, Refine::Infer),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Ty::Refine(BaseTy::Int, Refine::Infer),
            ty::TyKind::Ref(_, ty, mutability) => {
                // Rust won't allow having an initialized reference to uninitialized memory, so we
                // assume everything is initialized from now on.
                let ty = self.lower_initialized(ty);
                let l = self.names.fresh_location();
                self.heap.push((l, ty));
                match mutability {
                    Mutability::Mut => Ty::Ref(BorrowKind::Mut, Region::Infer, l),
                    Mutability::Not => Ty::Ref(BorrowKind::Shared, Region::Infer, l),
                }
            }
            _ => todo!(),
        }
    }

    fn lower_initialized(&mut self, ty: ty::Ty<'tcx>) -> Ty {
        match ty.kind() {
            ty::TyKind::Tuple(subst) if !subst.is_empty() => Ty::Tuple(
                ty.tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| (Field::new(i), self.lower_initialized(ty)))
                    .collect(),
            ),
            ty::TyKind::Tuple(_) => Ty::unit(),
            ty::TyKind::Bool => Ty::Refine(BaseTy::Bool, Refine::Infer),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Ty::Refine(BaseTy::Int, Refine::Infer),
            ty::TyKind::Ref(_, ty, mutability) => {
                let ty = self.lower_initialized(ty);
                let l = self.names.fresh_location();
                self.heap.push((l, ty));
                match mutability {
                    Mutability::Mut => Ty::Ref(BorrowKind::Mut, Region::Infer, l),
                    Mutability::Not => Ty::Ref(BorrowKind::Shared, Region::Infer, l),
                }
            }
            _ => todo!(),
        }
    }

    fn lower_uninitialized(&mut self, ty: ty::Ty<'tcx>) -> Ty {
        match ty.kind() {
            ty::TyKind::Tuple(subst) if !subst.is_empty() => {
                let tup = ty
                    .tuple_fields()
                    .enumerate()
                    .map(|(i, ty)| (Field::new(i), self.lower_uninitialized(ty)))
                    .collect();
                Ty::Tuple(tup)
            }
            ty::TyKind::Tuple(_)
            | ty::TyKind::Bool
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Ref(..) => Ty::Uninit(1),
            _ => todo!(),
        }
    }

    fn is_maybe_unitialized(&self, projection: &[mir::PlaceElem<'tcx>]) -> bool {
        let place = PlaceRef {
            local: self.local,
            projection,
        };
        let move_path_index = match self.move_data.rev_lookup.find(place) {
            LookupResult::Exact(move_path_index) | LookupResult::Parent(Some(move_path_index)) => {
                move_path_index
            }
            LookupResult::Parent(None) => bug!(),
        };
        self.maybe_uninitialized_cursor
            .get()
            .contains(move_path_index)
    }
}

struct NameProducer {
    next_location: usize,
    next_local: usize,
}

impl NameProducer {
    fn new(body: &mir::Body) -> Self {
        Self {
            next_location: 0,
            next_local: body.local_decls.len(),
        }
    }

    fn fresh_local(&mut self) -> Local {
        self.next_local += 1;
        Local::new(self.next_local - 1)
    }

    fn fresh_location(&mut self) -> Location {
        self.next_location += 1;
        Location::new(self.next_location - 1)
    }
}
