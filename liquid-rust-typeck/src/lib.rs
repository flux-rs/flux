#![feature(rustc_private, min_specialization, once_cell, generic_associated_types)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

mod checker;
mod constraint_gen;
mod dbg;
pub mod global_env;
mod intern;
pub mod lowering;
mod pretty;
mod pure_ctxt;
mod subst;
pub mod ty;
mod type_env;
pub mod wf;

use std::{fs, io::Write, str::FromStr};

use checker::Checker;
use constraint_gen::Tag;
use global_env::GlobalEnv;
use itertools::Itertools;
use liquid_rust_common::{
    config::CONFIG,
    errors::ErrorReported,
    index::{IndexGen, IndexVec},
};
use liquid_rust_core::ir::Body;
use liquid_rust_fixpoint::{self as fixpoint, FixpointResult};
use pure_ctxt::KVarStore;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use ty::Name;

pub struct FixpointCtxt {
    kvars: KVarStore,
    name_gen: IndexGen<fixpoint::Name>,
    name_map: FxHashMap<Name, fixpoint::Name>,
    tags: IndexVec<TagIdx, Tag>,
    tags_inv: FxHashMap<Tag, TagIdx>,
}

newtype_index! {
    pub struct TagIdx {
        DEBUG_FORMAT = "TagIdx({})"
    }
}

pub fn check<'tcx>(
    genv: &GlobalEnv<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    qualifiers: &[ty::Qualifier],
) -> Result<(), ErrorReported> {
    let bb_envs = Checker::infer(genv, body, def_id)?;
    let mut kvars = KVarStore::new();
    let pure_cx = Checker::check(genv, body, def_id, &mut kvars, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(genv.tcx, def_id, &pure_cx, ".lrc").unwrap();
    }

    let mut fcx = FixpointCtxt::new(kvars);

    let constraint = pure_cx.into_fixpoint(&mut fcx);

    fcx.check(genv.tcx, def_id, body.mir.span, constraint, qualifiers)
}

impl FixpointCtxt {
    pub fn new(kvars: KVarStore) -> Self {
        Self {
            kvars,
            name_gen: IndexGen::new(),
            name_map: FxHashMap::default(),
            tags: IndexVec::new(),
            tags_inv: FxHashMap::default(),
        }
    }

    pub fn with_name_map<R>(
        &mut self,
        name: Name,
        to: fixpoint::Name,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.name_map.insert(name, to);
        let r = f(self);
        self.name_map.remove(&name);
        r
    }

    fn fresh_name(&self) -> fixpoint::Name {
        self.name_gen.fresh()
    }

    fn check(
        self,
        tcx: TyCtxt,
        did: DefId,
        body_span: Span,
        constraint: fixpoint::Constraint<TagIdx>,
        qualifiers: &[ty::Qualifier],
    ) -> Result<(), ErrorReported> {
        let kvars = self.kvars.into_fixpoint();

        let qualifiers = qualifiers.iter().map(qualifier_into_fixpoint).collect();

        let task = fixpoint::Task::new(kvars, constraint, qualifiers);
        if CONFIG.dump_constraint {
            dump_constraint(tcx, did, &task, ".smt2").unwrap();
        }

        match task.check() {
            Ok(FixpointResult::Safe(_)) => Ok(()),
            Ok(FixpointResult::Unsafe(_, errors)) => {
                let errors = errors
                    .into_iter()
                    .map(|err| self.tags[err.tag])
                    .unique()
                    .collect_vec();

                report_errors(tcx, body_span, errors)
            }
            Ok(FixpointResult::Crash(err)) => panic!("fixpoint crash: {err:?}"),
            Err(err) => panic!("failed to run fixpoint: {err:?}"),
        }
    }

    fn tag_idx(&mut self, tag: Tag) -> TagIdx {
        *self
            .tags_inv
            .entry(tag)
            .or_insert_with(|| self.tags.push(tag))
    }
}

fn report_errors(tcx: TyCtxt, body_span: Span, errors: Vec<Tag>) -> Result<(), ErrorReported> {
    for err in errors {
        match err {
            Tag::Call(span) => tcx.sess.emit_err(errors::CallError { span }),
            Tag::Assign(span) => tcx.sess.emit_err(errors::AssignError { span }),
            Tag::Ret => tcx.sess.emit_err(errors::RetError { span: body_span }),
            Tag::Div(span) => tcx.sess.emit_err(errors::DivError { span }),
            Tag::Rem(span) => tcx.sess.emit_err(errors::RemError { span }),
            Tag::Goto(span, bb) => tcx.sess.emit_err(errors::GotoError { span, bb }),
        };
    }

    Err(ErrorReported)
}

fn dump_constraint<C: std::fmt::Debug>(
    tcx: TyCtxt,
    def_id: DefId,
    c: &C,
    suffix: &str,
) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(format!("{}{}", tcx.def_path_str(def_id), suffix)))?;
    write!(file, "{:?}", c)
}

impl std::fmt::Display for TagIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_u32())
    }
}

impl FromStr for TagIdx {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_u32(s.parse()?))
    }
}

mod errors {
    use liquid_rust_core::ir::BasicBlock;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct GotoError {
        #[message = "error jumping to join point: `{bb:?}`"]
        pub span: Option<Span>,
        pub bb: BasicBlock,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct CallError {
        #[message = "precondition might not hold"]
        #[label = "precondition might not hold in this function call"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct AssignError {
        #[message = "missmatched type in assignment"]
        #[label = "this assignment might be unsafe"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RetError {
        #[message = "postcondition might not hold"]
        #[label = "the postcondition in this function might not hold"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DivError {
        #[message = "possible division by zero"]
        #[label = "denominator might not be zero"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RemError {
        #[message = "possible reminder with a divisor of zero"]
        #[label = "divisor might not be zero"]
        pub span: Span,
    }
}

fn qualifier_into_fixpoint(qualifier: &ty::Qualifier) -> fixpoint::Qualifier {
    let name_gen = IndexGen::new();
    let mut name_map = FxHashMap::default();
    let name = qualifier.name.clone();
    let args = qualifier
        .args
        .iter()
        .map(|(name, sort)| {
            let fresh_name = name_gen.fresh();
            name_map.insert(*name, fresh_name);
            let sort = sort_to_fixpoint(sort);
            (fresh_name, sort)
        })
        .collect();

    let expr = expr_to_fixpoint(&qualifier.expr, &name_map);
    fixpoint::Qualifier { name, args, expr }
}

fn sort_to_fixpoint(sort: &ty::Sort) -> fixpoint::Sort {
    match sort.kind() {
        ty::SortKind::Bool => fixpoint::Sort::Bool,
        ty::SortKind::Int => fixpoint::Sort::Int,
        _ => {
            unreachable!("Internal error: Bad sort kind in qualifier");
        }
    }
}

fn expr_to_fixpoint(
    expr: &ty::Expr,
    name_map: &FxHashMap<ty::Name, fixpoint::Name>,
) -> fixpoint::Expr {
    match expr.kind() {
        ty::ExprKind::BinaryOp(bop, expr1, expr2) => {
            let bop = bop_to_fixpoint(bop);
            let expr1 = expr_to_fixpoint(expr1, name_map);
            let expr2 = expr_to_fixpoint(expr2, name_map);
            fixpoint::Expr::BinaryOp(bop, Box::new(expr1), Box::new(expr2))
        }
        ty::ExprKind::Constant(constant) => {
            let constant = match constant {
                ty::Constant::Bool(b) => fixpoint::Constant::Bool(*b),
                ty::Constant::Int(sign, i) => fixpoint::Constant::Int(*sign, *i),
            };
            fixpoint::Expr::Constant(constant)
        }
        ty::ExprKind::Var(var) => {
            match var {
                ty::Var::Free(name) => {
                    let name = name_map.get(name).unwrap_or_else(|| {
                        unreachable!(
                            "Internal error: Undeclared variable in qualifier: {:?}",
                            name
                        );
                    });
                    fixpoint::Expr::Var(*name)
                }
                ty::Var::Bound(_) => {
                    unreachable!("Internal error: Bound variable in qualifier");
                }
            }
        }
        _ => {
            unreachable!("Internal error: Bad ExprKind variable in qualifier");
        }
    }
}

fn bop_to_fixpoint(bop: &ty::BinOp) -> fixpoint::BinOp {
    match bop {
        ty::BinOp::Add => fixpoint::BinOp::Add,
        ty::BinOp::And => fixpoint::BinOp::And,
        ty::BinOp::Div => fixpoint::BinOp::Div,
        ty::BinOp::Eq => fixpoint::BinOp::Eq,
        ty::BinOp::Ge => fixpoint::BinOp::Ge,
        ty::BinOp::Gt => fixpoint::BinOp::Gt,
        ty::BinOp::Iff => fixpoint::BinOp::Iff,
        ty::BinOp::Imp => fixpoint::BinOp::Imp,
        ty::BinOp::Le => fixpoint::BinOp::Le,
        ty::BinOp::Lt => fixpoint::BinOp::Lt,
        ty::BinOp::Mod => fixpoint::BinOp::Mod,
        ty::BinOp::Mul => fixpoint::BinOp::Mul,
        ty::BinOp::Ne => fixpoint::BinOp::Ne,
        ty::BinOp::Or => fixpoint::BinOp::Or,
        ty::BinOp::Sub => fixpoint::BinOp::Sub,
    }
}
