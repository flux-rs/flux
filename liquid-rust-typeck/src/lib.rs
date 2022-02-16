#![feature(rustc_private, min_specialization, once_cell)]

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
pub mod global_env;
mod intern;
mod lowering;
mod pretty;
mod pure_ctxt;
mod subst;
mod subtyping;
pub mod ty;
mod type_env;
pub mod wf;

use std::{fs, io::Write, str::FromStr};

use checker::Checker;
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
use subtyping::Tag;
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
) -> Result<(), ErrorReported> {
    let fn_sig = genv.lookup_fn_sig(def_id);

    let bb_envs = Checker::infer(genv, body, fn_sig)?;
    let (pure_cx, kvars) = Checker::check(genv, body, fn_sig, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(genv.tcx, def_id, &pure_cx, "").unwrap();
    }

    let mut fcx = FixpointCtxt::new(kvars);

    let constraint = pure_cx.into_fixpoint(&mut fcx);

    fcx.check(genv.tcx, def_id, body.mir.span, constraint)
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

    fn fresh_name(&self) -> fixpoint::Name {
        self.name_gen.fresh()
    }

    fn check(
        self,
        tcx: TyCtxt,
        did: DefId,
        body_span: Span,
        constraint: fixpoint::Constraint<TagIdx>,
    ) -> Result<(), ErrorReported> {
        let kvars = self.kvars.into_fixpoint();
        let task = fixpoint::Task::new(kvars, constraint);
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
            Tag::Goto(span) => tcx.sess.emit_err(errors::GotoError { span }),
        }
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
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct GotoError {
        #[message = "error jumping to join point"]
        pub span: Option<Span>,
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
