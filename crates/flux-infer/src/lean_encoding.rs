use std::{
    fs::{self, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use flux_common::{
    dbg::{self, SpanTrace},
    result::ResultExt,
};
use flux_config as config;
use flux_middle::{
    def_id::{FluxDefId, MaybeExternId},
    global_env::GlobalEnv,
    queries::QueryErr,
    rty::{PrettyMap, local_deps},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::ErrorGuaranteed;

use crate::{
    fixpoint_encoding::{FunDeps, KVarSolutions, SortDeps, fixpoint},
    lean_format::{self, LeanCtxt, WithLeanCtxt, def_id_to_pascal_case, snake_case_to_pascal_case},
};

/// Helper macro to create Vec<String> from string-like values
macro_rules! string_vec {
    ($($s:expr),* $(,)?) => {
        vec![$($s.to_string()),*]
    };
}

fn vc_name(genv: GlobalEnv, def_id: DefId) -> String {
    def_id_to_pascal_case(&def_id, &genv.tcx())
}

fn base(genv: GlobalEnv) -> PathBuf {
    genv.tcx()
        .sess
        .opts
        .working_dir
        .local_path_if_available()
        .to_path_buf()
        .join(config::lean_dir())
}

fn project() -> String {
    config::lean_project().to_string()
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

pub fn finalize(genv: GlobalEnv) -> io::Result<()> {
    let project = project();
    let src = genv.temp_dir().path().join(&project);
    let dst = base(genv).join(&project);
    rename_dir_contents(&src, &dst)
}

fn project_path(genv: GlobalEnv, kind: FileKind) -> PathBuf {
    let project = project();
    match kind {
        FileKind::Flux => genv.temp_dir().path().join(project),
        FileKind::User => base(genv).join(project),
    }
}

fn run_lean(genv: GlobalEnv, def_id: DefId) -> io::Result<()> {
    let proof_path = LeanFile::Proof(def_id).path(genv);
    let out = Command::new("lake")
        .arg("--quiet")
        .arg("lean")
        .arg(proof_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .current_dir(project_path(genv, FileKind::User))
        .spawn()?
        .wait_with_output()?;
    if out.stderr.is_empty() && out.stdout.is_empty() {
        Ok(())
    } else {
        let stderr =
            std::str::from_utf8(&out.stderr).unwrap_or("Lean exited with a non-zero return code");
        Err(io::Error::other(stderr))
    }
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
    /// "Root" of the lean project, importing all the generated proofs
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
    /// (machine) propositions holding the flux VCs
    Vc(DefId),
    /// (human) interactively written proofs of flux VCs
    Proof(DefId),
}

impl LeanFile {
    fn kind(&self) -> FileKind {
        match self {
            LeanFile::Basic
            | LeanFile::Fluxlib
            | LeanFile::Vc(_)
            | LeanFile::Fun(_)
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
            LeanFile::Vc(def_id) => {
                let name = vc_name(genv, *def_id);
                string_vec![project_name, "Flux", "VC", name]
            }
            LeanFile::Proof(def_id) => {
                let name = format!("{}Proof", vc_name(genv, *def_id));
                string_vec![project_name, "User", "Proof", name]
            }
        }
    }

    /// All paths should be generated here
    fn path(&self, genv: GlobalEnv) -> PathBuf {
        let mut path = project_path(genv, self.kind());
        for segment in self.segments(genv) {
            path = path.join(segment);
        }
        path.set_extension("lean");
        path
    }
}

pub struct LeanEncoder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: MaybeExternId,
    pretty_var_map: PrettyMap<fixpoint::LocalVar>,
    sort_deps: SortDeps,
    fun_deps: FunDeps,
    kvar_decls: Vec<fixpoint::KVarDecl>,
    constraint: fixpoint::Constraint,
    sort_files: FxHashMap<fixpoint::DataSort, LeanFile>,
    fun_files: FxHashMap<FluxDefId, LeanFile>,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    fn lean_cx(&self) -> LeanCtxt<'_, 'genv, 'tcx> {
        LeanCtxt {
            genv: self.genv,
            pretty_var_map: &self.pretty_var_map,
            adt_map: &self.sort_deps.adt_map,
        }
    }

    fn datasort_name(&self, sort: &fixpoint::DataSort) -> String {
        let name = format!("{}", WithLeanCtxt { item: sort, cx: &self.lean_cx() });
        snake_case_to_pascal_case(&name)
    }

    fn var_name(&self, var: &fixpoint::Var) -> String {
        let name = format!("{}", WithLeanCtxt { item: var, cx: &self.lean_cx() });
        snake_case_to_pascal_case(&name)
    }

    fn import(&self, file: &LeanFile) -> String {
        format!("import {}", file.segments(self.genv).join("."))
    }

    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        sort_deps: SortDeps,
        fun_deps: FunDeps,
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
    ) -> Result<Self, io::Error> {
        let mut encoder = Self {
            genv,
            def_id,
            pretty_var_map,
            sort_deps,
            fun_deps,
            kvar_decls,
            constraint,
            fun_files: FxHashMap::default(),
            sort_files: FxHashMap::default(),
        };
        encoder.fun_files = encoder.fun_files();
        encoder.sort_files = encoder.sort_files();
        Ok(encoder)
    }

    fn run(&self, kvar_solutions: KVarSolutions) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_if_absent()?;
        self.generate_vc_file(kvar_solutions)?;
        self.generate_proof_if_absent()?;
        self.record_proof()?;
        Ok(())
    }

    fn fun_files(&self) -> FxHashMap<FluxDefId, LeanFile> {
        let mut res = FxHashMap::default();
        for (did, opaque_fun) in &self.fun_deps.opaque_funs {
            let name = self.var_name(&opaque_fun.name);
            let file = LeanFile::OpaqueFun(name);
            res.insert(*did, file);
        }
        for (did, fun_def) in &self.fun_deps.fun_defs {
            let name = self.var_name(&fun_def.name);
            let file = LeanFile::Fun(name);
            res.insert(*did, file);
        }
        res
    }

    fn sort_files(&self) -> FxHashMap<fixpoint::DataSort, LeanFile> {
        let mut res = FxHashMap::default();
        for sort in &self.sort_deps.opaque_sorts {
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

    fn generate_lake_project_if_not_present(&self) -> Result<(), io::Error> {
        let path = project_path(self.genv, FileKind::User);
        if !path.exists() {
            Command::new("lake")
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
    ) -> Result<(), io::Error> {
        let name = self.datasort_name(&sort.name);
        let file = &LeanFile::OpaqueSort(name);

        let path = file.path(self.genv);
        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            writeln!(file, "def {} := sorry", WithLeanCtxt { item: sort, cx: &self.lean_cx() })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn opaque_fun_dependencies(&self, opaque_fun: &fixpoint::ConstDecl) -> Vec<&LeanFile> {
        let name = &opaque_fun.name;
        let mut acc = vec![];
        opaque_fun.sort.deps(&mut acc);
        acc.into_iter()
            .map(|data_sort| {
                self.sort_files.get(&data_sort).unwrap_or_else(|| {
                    panic!(
                        "Missing sort file for dependency {:?} of opaque fun {:?}",
                        data_sort, name
                    )
                })
            })
            .unique()
            .collect()
    }

    fn generate_opaque_fun_file_if_not_present(
        &self,
        opaque_fun: &fixpoint::ConstDecl,
    ) -> Result<(), io::Error> {
        let name = self.var_name(&opaque_fun.name);
        let file = &LeanFile::OpaqueFun(name);
        let path = file.path(self.genv);
        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            for dep in self.opaque_fun_dependencies(opaque_fun) {
                writeln!(file, "{}", self.import(dep))?;
            }
            writeln!(
                file,
                "def {} := sorry",
                WithLeanCtxt { item: opaque_fun, cx: &self.lean_cx() }
            )?;
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
    ) -> Result<(), io::Error> {
        let name = self.datasort_name(&data_decl.name);
        let file = &LeanFile::Struct(name);
        let path = file.path(self.genv);
        // No need to regenerate if created in this session; but otherwise regenerate as struct may have changed
        if let Some(mut file) = create_file_with_dirs(path)? {
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.data_decl_dependencies(data_decl) {
                writeln!(file, "{}", self.import(dep))?;
            }
            // write data decl
            writeln!(file, "{}", WithLeanCtxt { item: data_decl, cx: &self.lean_cx() })?;
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

    fn fun_def_dependencies(&self, did: &FluxDefId, fun_def: &fixpoint::FunDef) -> Vec<&LeanFile> {
        let mut res = vec![];

        // 1. Collect the sort dependencies
        let mut sorts = vec![];
        for (_, sort) in &fun_def.args {
            sort.deps(&mut sorts);
        }
        fun_def.out.deps(&mut sorts);
        for data_sort in sorts {
            res.push(self.sort_file(&data_sort));
        }

        // 2. Collect the fun dependencies
        let info = self.genv.normalized_info(*did);
        for dep_id in local_deps(&info.body) {
            res.push(self.fun_file(&dep_id.to_def_id()));
        }
        res
    }

    fn generate_fun_def_file_if_not_present(
        &self,
        did: &FluxDefId,
        fun_def: &fixpoint::FunDef,
    ) -> Result<(), io::Error> {
        let name = self.var_name(&fun_def.name);
        let path = LeanFile::Fun(name).path(self.genv);
        if let Some(mut file) = create_file_with_dirs(path)? {
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.fun_def_dependencies(did, fun_def) {
                writeln!(file, "{}", self.import(dep))?;
            }
            // write fun def
            writeln!(file, "{}", WithLeanCtxt { item: fun_def, cx: &self.lean_cx() })?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn generate_lib_if_absent(&self) -> Result<(), io::Error> {
        let path = LeanFile::Fluxlib.path(self.genv);
        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "-- FLUX LIBRARY [DO NOT MODIFY] --")?;
            // TODO: Can't we write this from a single `write!` call?
            writeln!(
                file,
                "def BitVec_shiftLeft {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)"
            )?;
            writeln!(
                file,
                "def BitVec_ushiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)"
            )?;
            writeln!(
                file,
                "def BitVec_sshiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)"
            )?;
            writeln!(
                file,
                "def BitVec_uge {{ n : Nat }} (x y : BitVec n) := (BitVec.ult x y).not"
            )?;
            writeln!(
                file,
                "def BitVec_sge {{ n : Nat }} (x y : BitVec n) := (BitVec.slt x y).not"
            )?;
            writeln!(
                file,
                "def BitVec_ugt {{ n : Nat }} (x y : BitVec n) := (BitVec.ule x y).not"
            )?;
            writeln!(
                file,
                "def BitVec_sgt {{ n : Nat }} (x y : BitVec n) := (BitVec.sle x y).not"
            )?;
            writeln!(
                file,
                "def SmtMap (t0 t1 : Type) [Inhabited t0] [BEq t0] [Inhabited t1] : Type := t0 -> t1"
            )?;
            writeln!(
                file,
                "def SmtMap_default {{ t0 t1: Type }} (v : t1) [Inhabited t0] [BEq t0] [Inhabited t1] : SmtMap t0 t1 := fun _ => v"
            )?;
            writeln!(
                file,
                "def SmtMap_store {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) (v : t1) : SmtMap t0 t1 :=\n  fun x => if x == k then v else m x"
            )?;
            writeln!(
                file,
                "def SmtMap_select {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) := m k"
            )?;
        }
        Ok(())
    }

    fn generate_vc_prelude(&self) -> Result<(), io::Error> {
        // 1. Generate lake project and lib file
        self.generate_lib_if_absent()?;

        // 2. Generate Opaque Struct Files
        for sort in &self.sort_deps.opaque_sorts {
            self.generate_opaque_sort_file_if_not_present(sort)?;
        }
        // 2. Generate Struct Files
        for data_decl in &self.sort_deps.data_decls {
            self.generate_struct_file_if_not_present(data_decl)?;
        }
        // 3. Generate Opaque Func Files
        for (_, opaque_fun) in &self.fun_deps.opaque_funs {
            self.generate_opaque_fun_file_if_not_present(opaque_fun)?;
        }
        // 4. Generate Func Def Files
        for (did, fun_def) in &self.fun_deps.fun_defs {
            self.generate_fun_def_file_if_not_present(did, fun_def)?;
        }
        Ok(())
    }

    fn generate_vc_imports(&self, file: &mut fs::File) -> io::Result<()> {
        writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;

        for sort in &self.sort_deps.opaque_sorts {
            let name = self.datasort_name(&sort.name);
            writeln!(file, "{}", self.import(&LeanFile::OpaqueSort(name)))?;
        }

        for data_decl in &self.sort_deps.data_decls {
            let name = self.datasort_name(&data_decl.name);
            writeln!(file, "{}", self.import(&LeanFile::Struct(name)))?;
        }

        for (_, opaque_fun) in &self.fun_deps.opaque_funs {
            let name = self.var_name(&opaque_fun.name);
            writeln!(file, "{}", self.import(&LeanFile::OpaqueFun(name)))?;
        }

        for (_, fun_def) in &self.fun_deps.fun_defs {
            let name = self.var_name(&fun_def.name);
            writeln!(file, "{}", self.import(&LeanFile::Fun(name)))?;
        }

        Ok(())
    }

    fn generate_vc_file(&self, kvar_solutions: KVarSolutions) -> Result<(), io::Error> {
        // 1. Generate imports
        self.generate_vc_prelude()?;

        // 2. Create file and add imports
        let def_id = self.def_id.resolved_id();
        let path = LeanFile::Vc(def_id).path(self.genv);
        if let Some(mut file) = create_file_with_dirs(path)? {
            self.generate_vc_imports(&mut file)?;

            let vc_name = vc_name(self.genv, def_id);
            // 3. Write the VC
            write!(
                file,
                "{}",
                WithLeanCtxt {
                    item: lean_format::LeanKConstraint {
                        theorem_name: &vc_name,
                        kvars: &self.kvar_decls,
                        constr: &self.constraint,
                        kvar_solutions,
                    },
                    cx: &self.lean_cx()
                }
            )?;
            file.sync_all()?;
        }

        Ok(())
    }

    fn generate_proof_if_absent(&self) -> Result<(), io::Error> {
        let def_id = self.def_id.resolved_id();
        let vc_name = vc_name(self.genv, def_id);
        let proof_name = format!("{vc_name}_proof");
        let path = LeanFile::Proof(def_id).path(self.genv);

        if let Some(span) = self.genv.proven_externally(self.def_id.local_id()) {
            let dst_span = SpanTrace::from_path(&path, 3, 5, proof_name.len());
            dbg::hyperlink_json!(self.genv.tcx(), span, dst_span);
        }

        if let Some(mut file) = create_file_with_dirs(path)? {
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            writeln!(file, "{}", self.import(&LeanFile::Vc(def_id)))?;
            writeln!(file, "def {proof_name} : {vc_name} := by")?;
            writeln!(file, "  unfold {vc_name}")?;
            writeln!(file, "  sorry")?;
            file.sync_all()?;
        }
        Ok(())
    }

    fn record_proof(&self) -> Result<(), io::Error> {
        let path = LeanFile::Basic.path(self.genv);

        let mut file = match create_file_with_dirs(&path)? {
            Some(mut file) => {
                // First invocation: reset VCs
                writeln!(file, "-- Flux Basic Imports [DO NOT MODIFY] --")?;
                file
            }
            None => fs::OpenOptions::new().append(true).open(path)?,
        };
        writeln!(file, "{}", self.import(&LeanFile::Proof(self.def_id.resolved_id())))
    }

    pub fn encode(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        deps: (SortDeps, FunDeps),
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
        kvar_solutions: KVarSolutions,
    ) -> Result<Self, io::Error> {
        let (sort_deps, fun_deps) = deps;
        let encoder =
            Self::new(genv, def_id, pretty_var_map, sort_deps, fun_deps, kvar_decls, constraint)?;
        encoder.run(kvar_solutions)?;
        Ok(encoder)
    }
}
