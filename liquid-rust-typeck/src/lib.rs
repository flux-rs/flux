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

use std::{
    fs,
    io::{self, Write},
};

use checker::Checker;
use global_env::GlobalEnv;
use liquid_rust_common::{
    config::CONFIG,
    errors::ErrorReported,
    index::{IndexGen, IndexVec},
};
use liquid_rust_core::ir::Body;
use liquid_rust_fixpoint::{self as fixpoint, FixpointResult, Safeness};
use pure_ctxt::{KVarStore, PureCtxt};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::newtype_index;
use rustc_middle::ty::TyCtxt;
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
    global_env: &GlobalEnv<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> Result<(), ErrorReported> {
    let fn_sig = global_env.lookup_fn_sig(def_id);

    let bb_envs = Checker::infer(global_env, body, fn_sig)?;
    let (pure_cx, kvars) = Checker::check(global_env, body, fn_sig, bb_envs)?;

    if CONFIG.dump_constraint {
        dump_constraint(global_env.tcx, def_id, &pure_cx).unwrap();
    }

    let mut fcx = FixpointCtxt::new(kvars);

    let constraint = pure_cx.into_fixpoint(&mut fcx);

    match fcx.check(constraint) {
        Ok(FixpointResult {
            tag: Safeness::Safe,
        }) => Ok(()),
        Ok(FixpointResult {
            tag: Safeness::Unsafe,
        }) => {
            global_env.tcx.sess.emit_err(errors::RefineError {
                span: body.mir.span,
            });
            Err(ErrorReported)
        }
        Ok(FixpointResult {
            tag: Safeness::Crash,
        }) => panic!("fixpoint crash"),
        Err(err) => panic!("failed to run fixpoint: {:?}", err),
    }
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

    fn check(self, constraint: fixpoint::Constraint<TagIdx>) -> io::Result<FixpointResult> {
        let kvars = self.kvars.into_fixpoint();
        let task = fixpoint::Task::new(kvars, constraint);
        task.check()
    }

    fn tag_idx(&mut self, tag: Tag) -> TagIdx {
        *self
            .tags_inv
            .entry(tag)
            .or_insert_with(|| self.tags.push(tag))
    }
}

fn dump_constraint(tcx: TyCtxt, def_id: DefId, cx: &PureCtxt) -> Result<(), std::io::Error> {
    let dir = CONFIG.log_dir.join("horn");
    fs::create_dir_all(&dir)?;
    let mut file = fs::File::create(dir.join(tcx.def_path_str(def_id)))?;
    write!(file, "{:?}", cx)
}

impl std::fmt::Display for TagIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_u32())
    }
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefineError {
        #[message = "unsafe function"]
        #[label = "this function is unsafe"]
        pub span: Span,
    }
}
