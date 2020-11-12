//! Handles the translation from Rust MIR to the CPS IR.

use super::ast::*;
use super::context::LiquidRustCtxt;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::{
        self,
        interpret::{ConstValue, Scalar},
        terminator::TerminatorKind,
        Body, PlaceRef, StatementKind,
    },
    ty::{self, ParamEnv},
};
use rustc_mir::{
    dataflow::{
        impls::MaybeUninitializedPlaces,
        move_paths::{LookupResult, MoveData, MovePathIndex},
        Analysis, MoveDataParamEnv,
    },
    transform::MirSource,
};
use rustc_span::Symbol;
use std::{collections::HashMap, convert::TryInto, mem::size_of};

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

// TODO: Mayhaps a Visitor pattern would be appropriate here

// First, we have to convert the MIR code to an SSA form.
// Once we do this, we can convert the SSA form into
// CPS form.

/// Translates an mir::Place to a CPS IR Place.
fn translate_place(from: &mir::Place) -> Place {
    let local = Local(Symbol::intern(format!("_{}", from.local.as_u32()).as_str()));
    let mut projection = vec![];

    for proj in from.projection {
        match proj {
            mir::ProjectionElem::Field(f, _ty) => projection.push(Projection::Field(f.as_u32())),
            mir::ProjectionElem::Deref => unimplemented!(),
            _ => todo!(),
        };
    }

    Place { local, projection }
}

fn translate_op(from: &mir::Operand) -> Operand {
    match from {
        mir::Operand::Copy(p) => Operand::Deref(translate_place(p)),
        mir::Operand::Move(p) => Operand::Deref(translate_place(p)),
        mir::Operand::Constant(bc) => translate_const(bc),
    }
}

// Adapted from
// https://github.com/rust-lang/rust/blob/master/compiler/rustc_middle/src/ty/print/pretty.rs
fn translate_const(from: &mir::Constant) -> Operand {
    match from.literal.val {
        ty::ConstKind::Value(value) => {
            match value {
                ConstValue::Scalar(s) => {
                    match (s, &from.literal.ty.kind) {
                        // Unit
                        (Scalar::Raw { size: 0, .. }, _t) => Operand::Constant(Constant::Unit),
                        // Bool
                        (Scalar::Raw { data: 0, .. }, ty::Bool) => {
                            Operand::Constant(Constant::Bool(false))
                        }
                        (Scalar::Raw { data: 1, .. }, ty::Bool) => {
                            Operand::Constant(Constant::Bool(true))
                        }
                        // TODO: Floats, when support is added
                        // Int
                        (Scalar::Raw { data, .. }, ty::Uint(_ui)) => {
                            Operand::Constant(Constant::Int(data))
                        }
                        // TODO: Signed ints, when support is added
                        // TODO: Chars, when support is added
                        _ => todo!("{:?}", from),
                    }
                }
                _ => todo!(),
            }
        }
        _ => todo!(),
    }
}

fn translate_rvalue<'tcx>(from: &mir::Rvalue<'tcx>) -> Rvalue {
    match from {
        mir::Rvalue::Use(op) => Rvalue::Use(translate_op(op)),
        mir::Rvalue::BinaryOp(op, a, b) => {
            Rvalue::BinaryOp((*op).into(), translate_op(a), translate_op(b))
        }
        mir::Rvalue::CheckedBinaryOp(op, a, b) => {
            Rvalue::CheckedBinaryOp((*op).into(), translate_op(a), translate_op(b))
        }
        _ => todo!(),
    }
}

impl From<mir::BinOp> for BinOp {
    fn from(op: mir::BinOp) -> BinOp {
        match op {
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
}

fn get_basic_type<'tcx>(t: ty::Ty<'tcx>) -> BasicType {
    match &t.kind {
        ty::TyKind::Bool => BasicType::Bool,
        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => BasicType::Int,
        _ => todo!(),
    }
}

// TODO: For some reason, TyS::size returns 1 for all scalar types
// Idk why, but once this is fixed, we'll actually get the size
// of types correctly

/// Gets the size of a type for use of creating an uninitalized type of that
/// sizer later. The type must be a scalar type - no tuples!
fn get_size<'tcx>(_t: ty::Ty<'tcx>) -> u32 {
    1
    // match &t.kind {
    //     ty::TyKind::Bool => size_of::<bool>().try_into().unwrap(),
    //     ty::TyKind::Int(it) => it.bit_width()
    //         .map(|x| x >> 3)
    //         .unwrap_or_else(|| size_of::<isize>().try_into().unwrap()) as u32,
    //     ty::TyKind::Uint(it) => it.bit_width()
    //         .map(|x| x >> 3 as u32)
    //         .unwrap_or_else(|| size_of::<isize>().try_into().unwrap()) as u32,
    //     _ => todo!(),
    // }
}

/// Creates a TypeLayout based on a Rust TyKind.
fn get_layout<'tcx>(t: ty::Ty<'tcx>) -> TypeLayout {
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
    match &t.kind {
        ty::TyKind::Tuple(_) => {
            TypeLayout::Tuple(t.tuple_fields().map(|c| get_layout(c)).collect::<Vec<_>>())
        }
        _ => TypeLayout::Block(1),
    }
}

// Transformer state struct should include a mapping from locals to refinements too

pub struct Transformer<'lr, 'tcx> {
    // TODO: What should the lifetime on this be?
    cps_cx: &'lr LiquidRustCtxt<'lr>,
    tcx: ty::TyCtxt<'tcx>,
    symbols: HashMap<Symbol, usize>,
}

impl<'lr, 'tcx> Transformer<'lr, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, cps_cx: &'lr LiquidRustCtxt<'lr>) -> Self {
        Self {
            cps_cx,
            tcx,
            symbols: HashMap::new(),
        }
    }

    /// Generates a fresh variable with a certain prefix.
    fn fresh(&mut self, prefix: Symbol) -> Symbol {
        // We look up our symbol in our map.
        // If it doesn't already exist, return it suffixed by 0.
        // Otherwise, return it with the correct prefix.
        // In both cases, we only return if the symbol with the suffix
        // also doesn't exist.

        let sym = if let Some(s) = self.symbols.get_mut(&prefix) {
            let sym = Symbol::intern(format!("{}{}", &prefix, *s).as_str());
            *s += 1;
            sym
        } else {
            let sym = Symbol::intern(format!("{}0", &prefix).as_str());
            self.init_sym(sym);
            sym
        };

        if self.symbols.get(&sym).is_none() {
            sym
        } else {
            self.fresh(sym)
        }
    }

    /// Records a symbol as being used
    fn init_sym(&mut self, sym: Symbol) {
        self.symbols.insert(sym, 1);
    }

    /// Based on the structure of the type, return either a RefineHole
    /// or a tuple of holy types.
    fn get_holy_type(&mut self, t: ty::Ty<'tcx>) -> Ty<'lr> {
        match &t.kind {
            ty::TyKind::Tuple(_) => self.cps_cx.mk_tuple(
                &t.tuple_fields()
                    .enumerate()
                    .map(|(i, f)| (Field::nth(i.try_into().unwrap()), self.get_holy_type(f)))
                    .collect::<Vec<_>>(),
            ),
            _ => self.cps_cx.mk_refine_hole(get_basic_type(t)),
        }
    }

    /// For a given local, based on the structure of its type and which
    /// of its parts are initialized, return either a RefineHole or an uninitalized
    /// block of the corresponding size, or a tuple of maybe holy types
    fn get_maybe_holy_type(
        &mut self,
        move_data: &MoveData<'tcx>,
        uninited: &BitSet<MovePathIndex>,
        l: mir::Local,
        ps: &mut Vec<mir::PlaceElem<'tcx>>,
        t: ty::Ty<'tcx>,
    ) -> Ty<'lr> {
        match &t.kind {
            ty::TyKind::Tuple(_) => self.cps_cx.mk_tuple(
                &t.tuple_fields()
                    .enumerate()
                    .map(|(i, f)| {
                        ps.push(mir::ProjectionElem::Field(mir::Field::from_usize(i), f));
                        let res = (
                            Field::nth(i.try_into().unwrap()),
                            self.get_maybe_holy_type(move_data, uninited, l, ps, f),
                        );
                        let _ = ps.pop();

                        res
                    })
                    .collect::<Vec<_>>(),
            ),
            _ => {
                let mpi = match move_data.rev_lookup.find(PlaceRef {
                    local: l,
                    projection: ps,
                }) {
                    LookupResult::Exact(ix) => ix,
                    LookupResult::Parent(Some(ix)) => ix,
                    LookupResult::Parent(None) => return self.cps_cx.mk_uninit(get_size(t)),
                };

                if uninited.contains(mpi) {
                    self.cps_cx.mk_uninit(get_size(t))
                } else {
                    self.cps_cx.mk_refine_hole(get_basic_type(t))
                }
            }
        }
    }

    // TODO: In later compiler versions, the MirSource is contained as a field
    // source within the Body
    /// Translates an MIR function body to a CPS IR FnDef.
    pub fn translate_body(&mut self, source: MirSource<'tcx>, body: &Body<'tcx>) -> FnDef<'lr> {
        let retk = self.fresh(Symbol::intern("_rk"));

        // The let-bound local representing the return value of the function
        let retv = Symbol::intern("_0");

        // We first perform dataflow analysis on our body to determine
        // which locals are initialized in which basic blocks, so that we can
        // set the types of the heap arguments of our basic blocks

        let param_env = self.tcx.param_env(source.def_id());
        let mdpe_move_data =
            MoveData::gather_moves(body, self.tcx, param_env).unwrap_or_else(|x| x.0);
        let move_data = MoveData::gather_moves(body, self.tcx, param_env).unwrap_or_else(|x| x.0);
        let mdpe = create_mpde(mdpe_move_data, param_env);

        let mut results = MaybeUninitializedPlaces::new(self.tcx, body, &mdpe)
            .into_engine(self.tcx, body, source.def_id())
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        // We then generate a jump instruction to jump to the continuation
        // corresponding to the first/root basic block, bb0.
        let mut nb = FnBody::Jump {
            target: Symbol::intern("bb0"),
            args: Vec::new(),
        };

        // We then iterate through our basic blocks
        // We don't need to do this in dom tree order because our bbs
        // should be mutually recursive
        for (bb, bbd) in body.basic_blocks().iter_enumerated() {
            // For each basic block, we generate a statement for the terminator first,
            // then we go through the statements in reverse, building onto the
            // FnBody this way.
            let mut bbod = match &bbd.terminator().kind {
                TerminatorKind::Goto { target } => FnBody::Jump {
                    target: Symbol::intern(format!("bb{}", target.as_u32()).as_str()),
                    args: Vec::new(),
                },
                // TODO: Actually do the asserting
                TerminatorKind::Assert { target, .. } => FnBody::Jump {
                    target: Symbol::intern(format!("bb{}", target.as_u32()).as_str()),
                    args: Vec::new(),
                },
                TerminatorKind::SwitchInt {
                    discr,
                    targets,
                    values,
                    switch_ty,
                    ..
                } => {
                    // We have to test our operand against each provided target value.
                    // This will turn into nested conditionals: if {} else { if ... }

                    // We first start with the else branch, since that's at the leaf of our
                    // if-else-if-else chain, and build backwards from there.
                    let mut tgs = targets.iter().rev();

                    let otherwise = tgs.next().unwrap();
                    let mut ite = FnBody::Jump {
                        target: Symbol::intern(format!("bb{}", otherwise.as_u32()).as_str()),
                        args: vec![],
                    };

                    // Then for each value remaining, we create a new FnBody::Ite, jumping to
                    // the specified target.
                    for (val, target) in values.iter().zip(tgs) {
                        // We first have to translate our discriminator into an AST Operand.
                        let op = translate_op(discr);

                        let then = FnBody::Jump {
                            target: Symbol::intern(format!("bb{}", target.as_u32()).as_str()),
                            args: vec![],
                        };

                        // We can only have places for guards, so we have
                        // to create a place first.
                        let sym = Local(self.fresh(Symbol::intern(format!("_g").as_str())));
                        // Bools are guaranteed to be one byte, so assuming a one byte
                        // TypeLayout should be ok!
                        let bind = Statement::Let(
                            sym,
                            TypeLayout::Block(size_of::<bool>().try_into().unwrap()),
                        );

                        let pl = Place {
                            local: sym,
                            projection: vec![],
                        };

                        // If the discr type is a bool, we compare to a bool constant.
                        // otherwise, compare with an int constant.
                        let is_bool = match switch_ty.kind {
                            ty::TyKind::Bool => true,
                            _ => false,
                        };
                        let asgn = Statement::Assign(
                            pl.clone(),
                            if !is_bool {
                                Rvalue::BinaryOp(
                                    BinOp::Eq,
                                    op,
                                    Operand::Constant(Constant::Int(*val)),
                                )
                            } else {
                                if *val != 0 {
                                    Rvalue::Use(op)
                                } else {
                                    Rvalue::UnaryOp(UnOp::Not, op)
                                }
                            },
                        );

                        ite = FnBody::Seq(
                            bind,
                            Box::new(FnBody::Seq(
                                asgn,
                                Box::new(FnBody::Ite {
                                    discr: pl,
                                    then: Box::new(then),
                                    else_: Box::new(ite),
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
                    target: retk,
                    args: vec![Local(retv)],
                },
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    // TODO: For now, we assume that all functions are constants (i.e. they're defined
                    // separately outside of this function. This isn't always true, however.

                    // We first get the destination basic block out of the destination; we'll
                    // do the assignment to the place after we have our FnBody::Call
                    // If destination is None, that means that this function doesn't converge;
                    // it diverges and never returns (i.e. returns ! and infinitely loops or smth)
                    // TODO: Perhaps handle the diverging case somehow?
                    let ret = match destination {
                        Some((_, bb)) => Symbol::intern(format!("_{}", bb.as_u32()).as_str()),
                        None => todo!(),
                    };

                    // For our args, our args will be a list of new temp locals that we create.
                    // We'll actually create these locals after we have our FnBody::Call, so that
                    // we can reference it.
                    let start_ix = *self
                        .symbols
                        .get(&Symbol::intern(format!("_farg").as_str()))
                        .unwrap_or(&0);
                    let new_args = (start_ix..start_ix + args.len())
                        .map(|i| Local(Symbol::intern(format!("_farg{}", i).as_str())))
                        .collect::<Vec<_>>();

                    let mut fb = match func {
                        mir::Operand::Constant(bc) => {
                            let c = &*bc;
                            let kind = &c.literal.ty.kind;

                            match kind {
                                ty::TyKind::FnDef(def_id, _) => {
                                    // We get the stringified name of this def,
                                    // then use it as the name of the function
                                    // we're calling.

                                    let fname = self.tcx.def_path_str(*def_id);
                                    let func = Place {
                                        local: Local(Symbol::intern(&fname)),
                                        projection: vec![],
                                    };

                                    // Finally, return our FnBody::Call!
                                    FnBody::Call {
                                        func,
                                        args: new_args,
                                        ret,
                                    }
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => todo!(),
                    };

                    // We now have to actually create and assign locals for our operands.
                    for arg in args {
                        // We let-define a new variable for our function arg, then
                        // assign it to the value of the arg.

                        let sym = Local(self.fresh(Symbol::intern(format!("_farg").as_str())));
                        let tys = arg.ty(body, self.tcx);
                        let bind = Statement::Let(sym, get_layout(&tys));

                        let pl = Place {
                            local: sym,
                            projection: vec![],
                        };
                        let assign = Statement::Assign(pl, Rvalue::Use(translate_op(arg)));
                        fb = FnBody::Seq(bind, Box::new(FnBody::Seq(assign, Box::new(fb))));
                    }

                    fb
                }
                TerminatorKind::Abort => FnBody::Abort,
                _ => todo!(),
            };

            for stmt in bbd.statements.iter().rev() {
                match &stmt.kind {
                    StatementKind::Assign(pr) => {
                        let place = translate_place(&pr.0);
                        let rval = translate_rvalue(&pr.1);

                        let stmt = Statement::Assign(place, rval);
                        bbod = FnBody::Seq(stmt, Box::new(bbod));
                    }

                    _ => { /* TODO? */ }
                };
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

            results.seek_to_block_start(bb);
            let uninited = results.get();

            let mut env = vec![];
            let mut heap = vec![];

            for (lix, decl) in body.local_decls.iter_enumerated() {
                let arg = Local(Symbol::intern(format!("_{}", lix.index()).as_str()));
                let loc = Location(Symbol::intern(format!("loc_{}", lix.index()).as_str()));

                // Check if this local has been initialized yet.
                let mut ps = vec![];
                let ty = self.get_maybe_holy_type(&move_data, &uninited, lix, &mut ps, decl.ty);

                env.push((arg, OwnRef(loc)));
                heap.push((loc, ty));
            }

            let lc = ContDef {
                name: Symbol::intern(format!("bb{}", bb.as_u32()).as_str()),
                heap,
                env,
                params: vec![],
                body: Box::new(bbod),
            };

            nb = FnBody::LetCont {
                def: lc,
                rest: Box::new(nb),
            };
        }

        // We finish by taking care of the let bindings - let binding all of the
        // locals in our MIR function body.
        // We do this because a FnBody::Sequence takes a statement and the rest
        // of the function body; we do this at the end so that we have a "rest of`
        // the function body"
        for (ix, decl) in body.local_decls.iter_enumerated().rev() {
            if (1..body.arg_count + 1).contains(&ix.index()) {
                // Skip over argument locals, they're printed in the signature.
                continue;
            }

            let sym = Local(Symbol::intern(format!("_{}", ix.as_u32()).as_str()));
            let s = Statement::Let(sym, get_layout(decl.ty));
            nb = FnBody::Seq(s, Box::new(nb));
        }

        // For our function definition, we need to record what arguments our
        // function takes
        // As with our continuation, our function args go in args; all of
        // the args are owned references to vars in the heap. Each of these
        // vars has a corresponding BasicType, refined with a RefineHole

        let mut args = vec![];
        let mut heap = vec![];

        for lix in body.args_iter() {
            let decl = &body.local_decls[lix];

            let arg = Local(Symbol::intern(format!("_{}", lix.index()).as_str()));
            let loc = Location(Symbol::intern(format!("loc_{}", lix.index()).as_str()));
            let ty = self.get_holy_type(decl.ty);

            args.push((arg, OwnRef(loc)));
            heap.push((loc, ty));
        }

        // Our return type is local _0; we want to get a holy type here as
        // our return type
        let out_loc = Location(Symbol::intern(format!("loc_0").as_str()));
        let out_tys = self.get_holy_type(body.local_decls[mir::Local::from_u32(0)].ty);
        heap.push((out_loc, out_tys));
        let out_ty = OwnRef(out_loc);

        // Return our translated body
        // TODO: Different out_heap than input heap?
        let ret = FnDef {
            name: Symbol::intern(self.tcx.def_path_str(source.def_id()).as_str()),
            heap: heap.clone(),
            args,
            ret: retk,
            out_heap: heap,
            out_ty,
            body: Box::new(nb),
        };

        ret
    }
}
