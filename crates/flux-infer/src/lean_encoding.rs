use std::{
    fs::{self, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use flux_common::{
    bug,
    dbg::{self, SpanTrace},
    result::ResultExt,
};
use flux_config as config;
use flux_middle::{
    def_id::{FluxDefId, MaybeExternId},
    global_env::GlobalEnv,
    queries::QueryErr,
    rty::{BinOp, BvSize, PrettyMap, Sort, local_deps},
};
use itertools::Itertools;
use rustc_data_structures::{fx::FxIndexSet, unord::UnordMap};
use rustc_hir::def_id::DefId;
use rustc_span::ErrorGuaranteed;

use crate::{
    fixpoint_encoding::{ConstDeps, InterpretedConst, SortDeps, fixpoint},
    lean_format::{self, LeanCtxt, WithLeanCtxt, def_id_to_pascal_case, snake_case_to_pascal_case},
};

fn sort_name_fragment(sort: &Sort) -> String {
    match sort {
        Sort::Int => "Int".to_string(),
        Sort::Bool => "Bool".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::BitVec(BvSize::Fixed(n)) => format!("Bv{n}"),
        Sort::BitVec(BvSize::Param(p)) => format!("BvParam{}", p.as_u32()),
        Sort::BitVec(BvSize::Infer(_)) => "BvInfer".to_string(),
        _ => {
            format!("{sort:?}")
                .chars()
                .filter(|c| c.is_alphanumeric())
                .collect()
        }
    }
}

fn prim_op_lean_name(op: &BinOp) -> String {
    match op {
        BinOp::Add(s) => format!("PrimOpAdd{}", sort_name_fragment(s)),
        BinOp::Sub(s) => format!("PrimOpSub{}", sort_name_fragment(s)),
        BinOp::Mul(s) => format!("PrimOpMul{}", sort_name_fragment(s)),
        BinOp::Div(s) => format!("PrimOpDiv{}", sort_name_fragment(s)),
        BinOp::Mod(s) => format!("PrimOpMod{}", sort_name_fragment(s)),
        BinOp::BitAnd(s) => format!("PrimOpBitAnd{}", sort_name_fragment(s)),
        BinOp::BitOr(s) => format!("PrimOpBitOr{}", sort_name_fragment(s)),
        BinOp::BitXor(s) => format!("PrimOpBitXor{}", sort_name_fragment(s)),
        BinOp::BitShl(s) => format!("PrimOpBitShl{}", sort_name_fragment(s)),
        BinOp::BitShr(s) => format!("PrimOpBitShr{}", sort_name_fragment(s)),
        BinOp::Gt(s) => format!("PrimOpGt{}", sort_name_fragment(s)),
        BinOp::Ge(s) => format!("PrimOpGe{}", sort_name_fragment(s)),
        BinOp::Lt(s) => format!("PrimOpLt{}", sort_name_fragment(s)),
        BinOp::Le(s) => format!("PrimOpLe{}", sort_name_fragment(s)),
        BinOp::Eq => "PrimOpEq".to_string(),
        BinOp::Ne => "PrimOpNe".to_string(),
        BinOp::And => "PrimOpAnd".to_string(),
        BinOp::Or => "PrimOpOr".to_string(),
        BinOp::Iff => "PrimOpIff".to_string(),
        BinOp::Imp => "PrimOpImp".to_string(),
    }
}

/// Helper macro to create Vec<String> from string-like values
macro_rules! string_vec {
    ($($s:expr),* $(,)?) => {
        vec![$($s.to_string()),*]
    };
}

fn vc_name(genv: GlobalEnv, def_id: DefId) -> String {
    def_id_to_pascal_case(&def_id, &genv.tcx())
}

fn proof_name(genv: GlobalEnv, def_id: DefId) -> String {
    format!("{}_proof", vc_name(genv, def_id))
}

fn project() -> String {
    config::lean_project().to_string()
}

fn namespaced<F>(f: &mut fs::File, w: F) -> io::Result<()>
where
    F: Fn(&mut fs::File) -> io::Result<()>,
{
    let namespace = "F";
    writeln!(f, "\nnamespace {namespace}\n")?;
    w(f)?;
    writeln!(f, "\nend {namespace}")
}

// Via Gemini: https://gemini.google.com/share/9027e898b136
/// Renames all files and directories from 'src' to 'dst'
fn rename_dir_contents(src: &Path, dst: &Path) -> io::Result<()> {
    // 1. Ensure the destination root exists
    if !dst.exists() {
        fs::create_dir_all(dst)?;
    }

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if file_type.is_dir() {
            // 2. If it's a directory, recurse
            rename_dir_contents(&src_path, &dst_path)?;
        } else {
            // 3. If it's a file, rename (overwrites if exists)
            // On Windows, this will fail if the target file is "in use"
            // TODO: how to FORCE overwrite on Windows?
            fs::rename(&src_path, &dst_path)?;
        }
    }
    Ok(())
}

fn constant_deps(expr: &fixpoint::Expr, acc: &mut FxIndexSet<fixpoint::Var>) {
    match expr {
        fixpoint::Expr::Var(v) if matches!(v, fixpoint::Var::Const(..)) => {
            acc.insert(*v);
        }
        fixpoint::Expr::App(func, _, args, _) => {
            constant_deps(func, acc);
            args.iter().for_each(|expr| constant_deps(expr, acc));
        }
        fixpoint::Expr::And(inner) | fixpoint::Expr::Or(inner) => {
            inner.iter().for_each(|expr| constant_deps(expr, acc));
        }
        fixpoint::Expr::Atom(_, inner)
        | fixpoint::Expr::BinaryOp(_, inner)
        | fixpoint::Expr::Imp(inner)
        | fixpoint::Expr::Iff(inner)
        | fixpoint::Expr::Let(_, inner) => {
            inner.iter().for_each(|expr| constant_deps(expr, acc));
        }
        fixpoint::Expr::IfThenElse(inner) => {
            inner.iter().for_each(|expr| constant_deps(expr, acc));
        }
        fixpoint::Expr::Quantifier(_, _, inner)
        | fixpoint::Expr::Neg(inner)
        | fixpoint::Expr::Not(inner)
        | fixpoint::Expr::IsCtor(_, inner) => {
            constant_deps(inner, acc);
        }
        fixpoint::Expr::Var(..) | fixpoint::Expr::Constant(..) | fixpoint::Expr::ThyFunc(..) => {}
        fixpoint::Expr::WKVar(..) => unimplemented!(),
    }
}

pub fn finalize(genv: GlobalEnv) -> io::Result<()> {
    let project = project();
    let src = genv.temp_dir().path().join(&project);
    let dst = final_project_path(genv);
    if src.exists() { rename_dir_contents(&src, &dst) } else { Ok(()) }
}

fn final_project_path(genv: GlobalEnv) -> PathBuf {
    genv.lean_parent_dir().join(project())
}

fn project_path(genv: GlobalEnv, kind: FileKind) -> PathBuf {
    let project = project();
    match kind {
        FileKind::Flux => genv.temp_dir().path().join(project),
        FileKind::User => final_project_path(genv),
    }
}

fn run_proof(genv: GlobalEnv, def_id: DefId) -> io::Result<()> {
    let proof_path = LeanFile::Proof(def_id).path(genv, true);
    let out = Command::new("lake")
        .arg("--quiet")
        .arg("--log-level=error")
        .arg("lean")
        .arg(proof_path)
        .arg("--")
        .arg("--json")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .current_dir(project_path(genv, FileKind::User))
        .spawn()?
        .wait_with_output()?;
    if !out.stderr.is_empty() {
        let stderr =
            std::str::from_utf8(&out.stderr).unwrap_or("Lean exited with a non-zero return code");
        return Err(io::Error::other(stderr));
    }
    let stdout = std::str::from_utf8(&out.stdout).unwrap_or("");
    if stdout.lines().any(|line| line.contains("\"hasSorry\"")) {
        return Err(io::Error::other("proof uses `sorry`"));
    }
    Ok(())
}

fn run_check(genv: GlobalEnv, def_id: DefId) -> io::Result<()> {
    let checking_path = LeanFile::Checking(def_id).path(genv, true);
    let status = Command::new("lake")
        .arg("--quiet")
        .arg("--log-level=error")
        .arg("lean")
        .arg(checking_path)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .current_dir(project_path(genv, FileKind::User))
        .spawn()?
        .wait()?;
    if status.success() {
        Ok(())
    } else {
        Err(io::Error::other("Lean exited with a non-zero exit code"))
    }
}

fn run_lean(genv: GlobalEnv, def_id: DefId) -> io::Result<()> {
    dbg::log_verbose!("FLUX running lean proof for {def_id:?}");
    run_proof(genv, def_id)?;
    run_check(genv, def_id)?;
    Ok(())
}

pub fn check_proof(genv: GlobalEnv, def_id: DefId) -> Result<(), ErrorGuaranteed> {
    run_lean(genv, def_id)
        .map_err(|_| {
            let name = genv.tcx().def_path(def_id).to_string_no_crate_verbose();
            let msg = format!("failed to check external proof for `crate{name}`");
            let span = genv.tcx().def_span(def_id);
            QueryErr::Emitted(genv.sess().dcx().handle().struct_span_err(span, msg).emit())
        })
        .emit(&genv)?;
    Ok(())
}

/// Create a file at the given path, creating any missing parent directories.
fn create_file_with_dirs<P: AsRef<Path>>(path: P) -> io::Result<Option<fs::File>> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    match OpenOptions::new().write(true).create_new(true).open(path) {
        Ok(file) => Ok(Some(file)),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => Ok(None),
        Err(e) => Err(e),
    }
}

/// Create or truncate a file at the given path, creating any missing parent directories.
fn create_or_truncate_file_with_dirs<P: AsRef<Path>>(path: P) -> io::Result<fs::File> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(path)
}

#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum FileKind {
    /// Files that are only written by Flux
    Flux,
    /// Files that are modified by users
    User,
}

/// Different kinds of Lean files
#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum LeanFile {
    /// "Root" of the lean project, importing all the generated checking files
    Basic,
    /// "builtin" definitions
    Fluxlib,
    /// (human) opaque flux sorts, to be defined by the user in Lean
    OpaqueSort(String),
    /// (machine) sorts generated from flux definitions
    Struct(String),
    /// (human) opaque flux functions, to be defined by the user in Lean
    OpaqueFun(String),
    /// (machine) functions generated from flux definitions
    Fun(String),
    /// (machine) opaque constant encoded as a Lean axiom
    OpaqueConst(String),
    /// (machine) propositions holding the flux VCs
    Vc(DefId),
    /// (human) interactively written proofs of flux VCs
    Proof(DefId),
    /// (machine) files checking that a proof has the expected theorem type
    Checking(DefId),
}

impl LeanFile {
    fn kind(&self) -> FileKind {
        match self {
            LeanFile::Basic
            | LeanFile::Fluxlib
            | LeanFile::Vc(_)
            | LeanFile::Checking(_)
            | LeanFile::Fun(_)
            | LeanFile::OpaqueConst(_)
            | LeanFile::Struct(_) => FileKind::Flux,
            LeanFile::OpaqueSort(_) | LeanFile::OpaqueFun(_) | LeanFile::Proof(_) => FileKind::User,
        }
    }

    fn segments(&self, genv: GlobalEnv) -> Vec<String> {
        let project_name = snake_case_to_pascal_case(&project());
        match self {
            LeanFile::Basic => {
                string_vec![project_name, "Basic"]
            }
            LeanFile::Fluxlib => {
                string_vec![project_name, "Flux", "Prelude"]
            }
            LeanFile::OpaqueSort(name) => {
                // let name = self.datasort_name(sort);
                string_vec![project_name, "User", "Struct", name]
            }
            LeanFile::Struct(name) => {
                // let name = self.datasort_name(sort);
                string_vec![project_name, "Flux", "Struct", name]
            }
            LeanFile::OpaqueFun(name) => {
                // let name = self.var_name(name);
                string_vec![project_name, "User", "Fun", name]
            }
            LeanFile::Fun(name) => {
                // let name = self.var_name(name);
                string_vec![project_name, "Flux", "Fun", name]
            }
            LeanFile::OpaqueConst(name) => {
                string_vec![project_name, "Flux", "Const", name]
            }
            LeanFile::Vc(def_id) => {
                let name = vc_name(genv, *def_id);
                string_vec![project_name, "Flux", "VC", name]
            }
            LeanFile::Proof(def_id) => {
                let name = format!("{}Proof", vc_name(genv, *def_id));
                string_vec![project_name, "User", "Proof", name]
            }
            LeanFile::Checking(def_id) => {
                let name = vc_name(genv, *def_id);
                string_vec![project_name, "Flux", "Checking", name]
            }
        }
    }

    /// All paths should be generated here
    fn path(&self, genv: GlobalEnv, force_final: bool) -> PathBuf {
        let mut path =
            if force_final { final_project_path(genv) } else { project_path(genv, self.kind()) };
        for segment in self.segments(genv) {
            path = path.join(segment);
        }
        path.set_extension("lean");
        path
    }

    pub fn import(&self, genv: GlobalEnv) -> String {
        format!("import {}", self.segments(genv).join("."))
    }
}

pub struct LeanEncoder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: MaybeExternId,
    pretty_var_map: PrettyMap<fixpoint::LocalVar>,
    sort_deps: SortDeps,
    fun_deps: Vec<fixpoint::FunDef>,
    constants: ConstDeps,
    kvar_decls: Vec<fixpoint::KVarDecl>,
    constraint: fixpoint::Constraint,
    sort_files: UnordMap<fixpoint::DataSort, LeanFile>,
    fun_files: UnordMap<FluxDefId, LeanFile>,
    const_files: UnordMap<fixpoint::Var, LeanFile>,
    primop_var_map: UnordMap<fixpoint::GlobalVar, String>,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    fn lean_cx(&self) -> LeanCtxt<'_, 'genv, 'tcx> {
        LeanCtxt {
            genv: self.genv,
            pretty_var_map: &self.pretty_var_map,
            adt_map: &self.sort_deps.adt_map,
            opaque_adt_map: &self.sort_deps.opaque_sorts,
            primop_var_map: &self.primop_var_map,
            hide_sort_vars: false,
        }
    }

    fn datasort_name(&self, sort: &fixpoint::DataSort) -> String {
        let name = format!("{}", WithLeanCtxt { item: sort, cx: &self.lean_cx() });
        snake_case_to_pascal_case(&name)
    }

    fn lean_file_for_fun(&self, fun: &fixpoint::FunDef) -> LeanFile {
        let name = self.var_name(&fun.name);
        if fun.body.is_some() { LeanFile::Fun(name) } else { LeanFile::OpaqueFun(name) }
    }

    fn lean_file_for_interpreted_const(&self, const_: &InterpretedConst) -> LeanFile {
        let name = self.var_name(&const_.0.name);
        LeanFile::Fun(name)
    }

    fn var_name(&self, var: &fixpoint::Var) -> String {
        let name = format!("{}", WithLeanCtxt { item: var, cx: &self.lean_cx() });
        snake_case_to_pascal_case(&name)
    }

    fn post_import_preamble(&self) -> &str {
        "open Classical\nset_option linter.unusedVariables false\n"
    }

    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        sort_deps: SortDeps,
        fun_deps: Vec<fixpoint::FunDef>,
        constants: ConstDeps,
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
    ) -> io::Result<Self> {
        let primop_var_map: UnordMap<fixpoint::GlobalVar, String> = constants
            .opaque
            .iter()
            .filter_map(|(decl, op)| {
                if let fixpoint::Var::Const(gvar, None) = decl.name {
                    Some((gvar, prim_op_lean_name(op)))
                } else {
                    None
                }
            })
            .collect();
        let mut encoder = Self {
            genv,
            def_id,
            pretty_var_map,
            sort_deps,
            fun_deps,
            constants,
            kvar_decls,
            constraint,
            fun_files: UnordMap::default(),
            sort_files: UnordMap::default(),
            const_files: UnordMap::default(),
            primop_var_map,
        };
        encoder.fun_files = encoder.fun_files();
        encoder.sort_files = encoder.sort_files();
        encoder.const_files = encoder.const_files();
        Ok(encoder)
    }

    fn run(&self) -> io::Result<()> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_if_absent()?;
        self.generate_vc_file()?;
        self.generate_proof_if_absent()?;
        self.generate_checking_file()?;
        Ok(())
    }

    fn fun_files(&self) -> UnordMap<FluxDefId, LeanFile> {
        let mut res = UnordMap::default();
        for fun_def in &self.fun_deps {
            let fixpoint::Var::Global(_, did) = fun_def.name else {
                bug!("expected global var with id")
            };
            let name = self.var_name(&fun_def.name);
            let file = LeanFile::Fun(name);
            res.insert(did, file);
        }
        res
    }

    fn sort_files(&self) -> UnordMap<fixpoint::DataSort, LeanFile> {
        let mut res = UnordMap::default();
        for (_, sort) in &self.sort_deps.opaque_sorts {
            let data_sort = sort.name.clone();
            let name = self.datasort_name(&sort.name);
            let file = LeanFile::OpaqueSort(name);
            res.insert(data_sort, file);
        }
        for data_decl in &self.sort_deps.data_decls {
            let data_sort = data_decl.name.clone();
            let name = self.datasort_name(&data_decl.name);
            let file = LeanFile::Struct(name);
            res.insert(data_sort, file);
        }
        res
    }

    fn const_files(&self) -> UnordMap<fixpoint::Var, LeanFile> {
        let mut res = UnordMap::default();
        for (decl, _) in &self.constants.interpreted {
            res.insert(decl.name, LeanFile::Fun(self.var_name(&decl.name)));
        }
        for (decl, op) in &self.constants.opaque {
            res.insert(decl.name, LeanFile::OpaqueConst(prim_op_lean_name(op)));
        }
        res
    }

    fn generate_lake_project_if_not_present(&self) -> io::Result<()> {
        let path = project_path(self.genv, FileKind::User).join("lakefile.toml");
        if !path.exists() {
            Command::new("lake")
                .current_dir(self.genv.lean_parent_dir())
                .arg("+v4.28.0")
                .arg("new")
                .arg(project())
                .arg("lib")
                .spawn()
                .and_then(|mut child| child.wait())
                .map(|_| ())?;
        }
        Ok(())
    }

    fn generate_opaque_sort_file_if_not_present(
        &self,
        sort: &fixpoint::SortDecl,
    ) -> io::Result<()> {
        let name = self.datasort_name(&sort.name);
        let file = &LeanFile::OpaqueSort(name);

        let path = file.path(self.genv, false);
        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "{}", &LeanFile::Fluxlib.import(self.genv))?;
            writeln!(file, "{}", self.post_import_preamble())?;
            namespaced(&mut file, |f| {
                writeln!(f, "def {} := sorry", WithLeanCtxt { item: sort, cx: &self.lean_cx() })
            })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn data_decl_dependencies(&self, data_decl: &fixpoint::DataDecl) -> Vec<&LeanFile> {
        let name = &data_decl.name;
        let mut acc = vec![];
        data_decl.deps(&mut acc);
        acc.into_iter()
            .map(|data_sort| {
                self.sort_files.get(&data_sort).unwrap_or_else(|| {
                    panic!(
                        "Missing sort file for dependency {:?} of data decl {:?}",
                        data_sort, name
                    )
                })
            })
            .unique()
            .collect()
    }

    fn generate_struct_file_if_not_present(
        &self,
        data_decl: &fixpoint::DataDecl,
    ) -> io::Result<()> {
        let name = self.datasort_name(&data_decl.name);
        let file = &LeanFile::Struct(name);
        let path = file.path(self.genv, false);
        // No need to regenerate if created in this session; but otherwise regenerate as struct may have changed
        if let Some(mut file) = create_file_with_dirs(path)? {
            // import prelude
            writeln!(file, "{}", &LeanFile::Fluxlib.import(self.genv))?;
            // import sort dependencies
            for dep in self.data_decl_dependencies(data_decl) {
                writeln!(file, "{}", dep.import(self.genv))?;
            }
            writeln!(file, "{}", self.post_import_preamble())?;

            // write data decl
            namespaced(&mut file, |f| {
                writeln!(f, "{}", WithLeanCtxt { item: data_decl, cx: &self.lean_cx() })
            })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn sort_file(&self, sort: &fixpoint::DataSort) -> &LeanFile {
        self.sort_files
            .get(sort)
            .unwrap_or_else(|| panic!("Missing sort file for sort {:?}", sort))
    }

    fn fun_file(&self, did: &FluxDefId) -> &LeanFile {
        self.fun_files
            .get(did)
            .unwrap_or_else(|| panic!("Missing fun file for fun {:?}", did))
    }

    fn const_file(&self, name: &fixpoint::Var) -> &LeanFile {
        self.const_files
            .get(name)
            .unwrap_or_else(|| panic!("Missing const file for const {name:?}"))
    }

    fn fun_def_dependencies(&self, did: FluxDefId, fun_def: &fixpoint::FunDef) -> Vec<&LeanFile> {
        let mut res = vec![];

        // 1. Collect the sort dependencies
        let mut sorts = vec![];
        fun_def.sort.deps(&mut sorts);
        for data_sort in sorts {
            res.push(self.sort_file(&data_sort));
        }

        // 2. Collect the fun dependencies
        if !self.genv.normalized_info(did).uif {
            let body = self.genv.inlined_body(did);
            for dep_id in local_deps(&body) {
                res.push(self.fun_file(&dep_id.to_def_id()));
            }
        }

        let mut deps = FxIndexSet::default();
        if let Some(body) = &fun_def.body {
            constant_deps(&body.expr, &mut deps);
        }
        for (decl, _) in &self.constants.interpreted {
            if deps.contains(&decl.name) {
                res.push(self.const_file(&decl.name));
            }
        }
        res
    }

    fn generate_fun_def_file_if_not_present(
        &self,
        did: FluxDefId,
        fun_def: &fixpoint::FunDef,
    ) -> io::Result<()> {
        let path = self.lean_file_for_fun(fun_def).path(self.genv, false);
        if let Some(mut file) = create_file_with_dirs(path)? {
            // import prelude
            writeln!(file, "{}", &LeanFile::Fluxlib.import(self.genv))?;
            // import sort dependencies
            for dep in self.fun_def_dependencies(did, fun_def) {
                writeln!(file, "{}", dep.import(self.genv))?;
            }
            writeln!(file, "{}", self.post_import_preamble())?;

            // write fun def
            namespaced(&mut file, |f| {
                writeln!(f, "{}", WithLeanCtxt { item: fun_def, cx: &self.lean_cx() })
            })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn generate_interpreted_const_file_if_not_present(
        &self,
        interpreted_const: &InterpretedConst,
    ) -> io::Result<()> {
        let (const_decl, _) = interpreted_const;
        let path = self
            .lean_file_for_interpreted_const(interpreted_const)
            .path(self.genv, false);
        if let Some(mut file) = create_file_with_dirs(path)? {
            // import prelude
            writeln!(file, "{}", &LeanFile::Fluxlib.import(self.genv))?;

            let mut sort_deps = vec![];
            const_decl.sort.deps(&mut sort_deps);
            for dep in sort_deps {
                writeln!(file, "{}", self.sort_file(&dep).import(self.genv))?;
            }

            writeln!(file, "{}", self.post_import_preamble())?;

            namespaced(&mut file, |f| {
                if let Some(comment) = &const_decl.comment {
                    writeln!(f, "--{comment}")?;
                }
                writeln!(f, "{}", WithLeanCtxt { item: interpreted_const, cx: &self.lean_cx() })
            })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn generate_opaque_const_file(
        &self,
        const_decl: &fixpoint::ConstDecl,
        op: &BinOp,
    ) -> io::Result<()> {
        let stable_name = prim_op_lean_name(op);
        let file = LeanFile::OpaqueConst(stable_name.clone());
        let path = file.path(self.genv, false);
        let mut file = create_or_truncate_file_with_dirs(path)?;
        writeln!(file, "{}", &LeanFile::Fluxlib.import(self.genv))?;

        let mut sort_deps = vec![];
        const_decl.sort.deps(&mut sort_deps);
        for dep in sort_deps {
            writeln!(file, "{}", self.sort_file(&dep).import(self.genv))?;
        }

        writeln!(file, "{}", self.post_import_preamble())?;

        namespaced(&mut file, |f| {
            if let Some(comment) = &const_decl.comment {
                writeln!(f, "--{comment}")?;
            }
            writeln!(
                f,
                "axiom {stable_name} : {}",
                WithLeanCtxt { item: &const_decl.sort, cx: &self.lean_cx() }
            )
        })?;
        file.sync_all()?;
        Ok(())
    }

    fn generate_lib_if_absent(&self) -> io::Result<()> {
        let path = LeanFile::Fluxlib.path(self.genv, false);
        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "-- FLUX LIBRARY [DO NOT MODIFY] --")?;
            // TODO: Can't we write this from a single `write!` call?
            writeln!(
                file,
                "abbrev BitVec_shiftLeft {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)"
            )?;
            writeln!(
                file,
                "abbrev BitVec_ushiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)"
            )?;
            writeln!(
                file,
                "abbrev BitVec_sshiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)"
            )?;
            writeln!(
                file,
                "abbrev BitVec_uge {{ n : Nat }} (x y : BitVec n) := (BitVec.ult x y).not"
            )?;
            writeln!(
                file,
                "abbrev BitVec_sge {{ n : Nat }} (x y : BitVec n) := (BitVec.slt x y).not"
            )?;
            writeln!(
                file,
                "abbrev BitVec_ugt {{ n : Nat }} (x y : BitVec n) := (BitVec.ule x y).not"
            )?;
            writeln!(
                file,
                "abbrev BitVec_sgt {{ n : Nat }} (x y : BitVec n) := (BitVec.sle x y).not"
            )?;
            writeln!(
                file,
                "abbrev BitVec_zeroExtend {{n : Nat}} (extra : Nat) (x : BitVec n) : BitVec (n + extra) := BitVec.zeroExtend (n + extra) x"
            )?;
            writeln!(
                file,
                "abbrev BitVec_signExtend {{n : Nat}} (extra : Nat) (x : BitVec n) : BitVec (n + extra) := BitVec.signExtend (n + extra) x"
            )?;
            writeln!(
                file,
                "abbrev SmtMap (t0 t1 : Type) [Inhabited t0] [BEq t0] [Inhabited t1] : Type := t0 -> t1"
            )?;
            writeln!(
                file,
                "abbrev SmtMap_default {{ t0 t1: Type }} (v : t1) [Inhabited t0] [BEq t0] [Inhabited t1] : SmtMap t0 t1 := fun _ => v"
            )?;
            writeln!(
                file,
                "abbrev SmtMap_store {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) (v : t1) : SmtMap t0 t1 :=\n  fun x => if x == k then v else m x"
            )?;
            writeln!(
                file,
                "abbrev SmtMap_select {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) := m k"
            )?;
        }
        Ok(())
    }

    fn generate_vc_prelude(&self) -> io::Result<()> {
        // 1. Generate lake project and lib file
        self.generate_lib_if_absent()?;

        // 2. Generate Opaque Struct Files
        for (_, sort) in &self.sort_deps.opaque_sorts {
            self.generate_opaque_sort_file_if_not_present(sort)?;
        }
        // 2. Generate Struct Files
        for data_decl in &self.sort_deps.data_decls {
            self.generate_struct_file_if_not_present(data_decl)?;
        }
        // 3. Generate Func Def Files
        for fun_def in &self.fun_deps {
            let fixpoint::Var::Global(_, did) = fun_def.name else {
                bug!("expected global var with id")
            };
            self.generate_fun_def_file_if_not_present(did, fun_def)?;
        }
        // 4. Generate Const Decl Files
        for const_decl in &self.constants.interpreted {
            self.generate_interpreted_const_file_if_not_present(const_decl)?;
        }
        // 5. Generate Opaque Const Files (primop axioms)
        for (const_decl, op) in &self.constants.opaque {
            self.generate_opaque_const_file(const_decl, op)?;
        }
        Ok(())
    }

    fn generate_vc_imports(&self, file: &mut fs::File) -> io::Result<()> {
        writeln!(file, "{}", LeanFile::Fluxlib.import(self.genv))?;

        for (_, sort) in &self.sort_deps.opaque_sorts {
            let name = self.datasort_name(&sort.name);
            writeln!(file, "{}", LeanFile::OpaqueSort(name).import(self.genv))?;
        }

        for data_decl in &self.sort_deps.data_decls {
            let name = self.datasort_name(&data_decl.name);
            writeln!(file, "{}", LeanFile::Struct(name).import(self.genv))?;
        }

        for fun_def in &self.fun_deps {
            writeln!(file, "{}", self.lean_file_for_fun(fun_def).import(self.genv))?;
        }

        for const_decl in &self.constants.interpreted {
            writeln!(
                file,
                "{}",
                self.lean_file_for_interpreted_const(const_decl)
                    .import(self.genv)
            )?;
        }

        for (_, op) in &self.constants.opaque {
            writeln!(file, "{}", LeanFile::OpaqueConst(prim_op_lean_name(op)).import(self.genv))?;
        }

        Ok(())
    }

    fn generate_vc_file(&self) -> io::Result<()> {
        // 1. Generate imports
        self.generate_vc_prelude()?;

        // 2. Create file and add imports
        let def_id = self.def_id.resolved_id();
        let path = LeanFile::Vc(def_id).path(self.genv, false);
        if let Some(mut file) = create_file_with_dirs(path)? {
            self.generate_vc_imports(&mut file)?;
            writeln!(file, "{}", self.post_import_preamble())?;

            let vc_name = vc_name(self.genv, def_id);
            // 3. Write the VC
            namespaced(&mut file, |f| {
                write!(
                    f,
                    "{}",
                    WithLeanCtxt {
                        item: lean_format::LeanKConstraint {
                            theorem_name: &vc_name,
                            kvars: &self.kvar_decls,
                            constr: &self.constraint,
                            should_fail: self
                                .def_id
                                .as_local()
                                .map(|def_id| self.genv.should_fail(def_id))
                                .unwrap_or(false)
                        },
                        cx: &self.lean_cx()
                    }
                )
            })?;
            file.sync_all()?;
        }

        Ok(())
    }

    fn generate_proof_if_absent(&self) -> io::Result<()> {
        let def_id = self.def_id.resolved_id();
        let vc_name = vc_name(self.genv, def_id);
        let proof_name = proof_name(self.genv, def_id);
        let path = LeanFile::Proof(def_id).path(self.genv, false);

        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "{}", LeanFile::Fluxlib.import(self.genv))?;
            writeln!(file, "{}", LeanFile::Vc(def_id).import(self.genv))?;
            writeln!(file, "{}", self.post_import_preamble())?;
            namespaced(&mut file, |f| {
                writeln!(f, "def {proof_name} : {vc_name} := by")?;
                writeln!(f, "  unfold {vc_name}")?;
                writeln!(f, "  sorry")
            })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn generate_checking_file(&self) -> io::Result<()> {
        let def_id = self.def_id.resolved_id();
        let vc_name = vc_name(self.genv, def_id);
        let proof_name = proof_name(self.genv, def_id);
        let path = LeanFile::Checking(def_id).path(self.genv, false);

        let mut file = create_or_truncate_file_with_dirs(path)?;
        writeln!(file, "{}", LeanFile::Vc(def_id).import(self.genv))?;
        writeln!(file, "{}", LeanFile::Proof(def_id).import(self.genv))?;
        writeln!(file)?;
        writeln!(file, "#check (F.{proof_name} : F.{vc_name})")?;
        file.sync_all()?;
        Ok(())
    }

    pub fn encode(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        sort_deps: SortDeps,
        fun_deps: Vec<fixpoint::FunDef>,
        constants: ConstDeps,
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
    ) -> io::Result<()> {
        let encoder = Self::new(
            genv,
            def_id,
            pretty_var_map,
            sort_deps,
            fun_deps,
            constants,
            kvar_decls,
            constraint,
        )?;
        encoder.run()?;
        Ok(())
    }
}

fn hyperlink_proof(genv: GlobalEnv, def_id: MaybeExternId) {
    let proof_name = proof_name(genv, def_id.resolved_id());
    let path = LeanFile::Proof(def_id.resolved_id()).path(genv, false);
    if let Some(span) = genv.proven_externally(def_id.local_id()) {
        let dst_span = SpanTrace::from_path(&path, 3, 5, proof_name.len());
        dbg::hyperlink_json!(genv.tcx(), span, dst_span);
    }
}

fn record_proof(genv: GlobalEnv, def_id: MaybeExternId) -> io::Result<()> {
    let path = LeanFile::Basic.path(genv, false);

    let mut file = match create_file_with_dirs(&path)? {
        Some(mut file) => {
            // First invocation: reset VCs
            writeln!(file, "-- Flux Basic Imports [DO NOT MODIFY] --")?;
            file
        }
        None => fs::OpenOptions::new().append(true).open(path)?,
    };
    writeln!(file, "{}", LeanFile::Checking(def_id.resolved_id()).import(genv))
}

/// We need to both hyperlink the proof (so users can easily jump to it)
/// and record the checking file in `Basic.lean` (so that it gets checked by `lake build`),
/// regardless of whether the proof was cached.
pub fn log_proof(genv: GlobalEnv, def_id: MaybeExternId) -> Result<(), ErrorGuaranteed> {
    hyperlink_proof(genv, def_id);
    record_proof(genv, def_id)
        .map_err(|_| {
            let name = genv
                .tcx()
                .def_path(def_id.resolved_id())
                .to_string_no_crate_verbose();
            let msg = format!("failed to record proof for `{name}`");
            let span = genv.tcx().def_span(def_id);
            QueryErr::Emitted(genv.sess().dcx().handle().struct_span_err(span, msg).emit())
        })
        .emit(&genv)?;
    Ok(())
}
