use std::{
    fs::{self},
    io::{self, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use flux_common::dbg::{self, SpanTrace};
use flux_config as config;
use flux_middle::{
    def_id::{FluxDefId, MaybeExternId},
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::{PrettyMap, local_deps},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
    fixpoint_encoding::{FunDeps, SortDeps, fixpoint},
    lean_format::{self, LeanCtxt, LeanSortVar, WithLeanCtxt},
};

/// Different kinds of Lean files
#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub enum LeanFile {
    /// "builtin" definitions
    Fluxlib,
    /// (human) opaque flux sorts, to be defined by the user in Lean
    OpaqueSort(fixpoint::DataSort),
    /// (machine) sorts generated from flux definitions
    Struct(fixpoint::DataSort),
    /// (human) opaque flux functions, to be defined by the user in Lean
    OpaqueFun(fixpoint::Var),
    /// (machine) functions generated from flux definitions
    Fun(fixpoint::Var),
    /// (machine) propositions holding the flux VCs
    VC,
    /// (human) interactively written proofs of flux VCs
    Proof,
}

fn create_file_with_dirs<P: AsRef<Path>>(path: P) -> io::Result<fs::File> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::File::create(path)
}

fn snake_case_to_pascal_case(snake: &str) -> String {
    snake
        .split('_')
        .filter(|s| !s.is_empty()) // skip empty segments (handles double underscores)
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect::<String>()
}

pub struct LeanEncoder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: MaybeExternId,
    base: PathBuf,
    project: String,
    pretty_var_map: PrettyMap<fixpoint::LocalVar>,
    sort_deps: SortDeps,
    fun_deps: FunDeps,
    kvar_decls: Vec<fixpoint::KVarDecl>,
    constraint: fixpoint::Constraint,
    sort_files: FxHashMap<fixpoint::DataSort, LeanFile>,
    fun_files: FxHashMap<FluxDefId, LeanFile>,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    fn datasort_name(&self, sort: &fixpoint::DataSort) -> String {
        let name = format!("{}", LeanSortVar(sort));
        snake_case_to_pascal_case(&name)
    }

    fn var_name(&self, var: &fixpoint::Var) -> String {
        let name = format!(
            "{}",
            WithLeanCtxt {
                item: var,
                cx: &LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map }
            }
        );
        snake_case_to_pascal_case(&name)
    }

    fn vc_name(&self) -> String {
        let name = self
            .genv
            .tcx()
            .def_path(self.def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_");
        snake_case_to_pascal_case(&name)
    }

    fn segments(&self, file: &LeanFile) -> Vec<String> {
        let project_name = snake_case_to_pascal_case(&self.project);
        match file {
            LeanFile::Fluxlib => {
                vec![project_name, "Fluxlib".to_string()]
            }
            LeanFile::OpaqueSort(sort) => {
                let name = self.datasort_name(sort);
                vec![project_name, "OpaqueStruct".to_string(), name]
            }
            LeanFile::Struct(sort) => {
                let name = self.datasort_name(sort);
                vec![project_name, "Struct".to_string(), name]
            }
            LeanFile::OpaqueFun(name) => {
                let name = self.var_name(name);
                vec![project_name, "OpaqueFun".to_string(), name]
            }
            LeanFile::Fun(name) => {
                let name = self.var_name(name);
                vec![project_name, "Fun".to_string(), name]
            }
            LeanFile::VC => {
                let name = self.vc_name();
                vec![project_name, "VC".to_string(), name]
            }
            LeanFile::Proof => {
                let name = self.vc_name();
                vec![project_name, "Proof".to_string(), name]
            }
        }
    }

    fn import(&self, file: &LeanFile) -> String {
        format!("import {}\n", self.segments(file).join("."))
    }

    /// All paths should be generated here
    fn path(&self, file: &LeanFile) -> PathBuf {
        let mut path = self.base.join(&self.project);
        for segment in self.segments(file) {
            path = path.join(segment);
        }
        path.set_extension("lean");
        path
    }

    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        sort_deps: SortDeps,
        fun_deps: FunDeps,
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
    ) -> Self {
        let base = genv
            .tcx()
            .sess
            .opts
            .working_dir
            .local_path_if_available()
            .to_path_buf()
            .join(config::lean_dir());
        let project = config::lean_project().to_string();

        let mut encoder = Self {
            genv,
            def_id,
            base,
            project,
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
        encoder
    }

    fn fun_files(&self) -> FxHashMap<FluxDefId, LeanFile> {
        let mut res = FxHashMap::default();
        for (did, opaque_fun) in &self.fun_deps.opaque_funs {
            let file = LeanFile::OpaqueFun(opaque_fun.name);
            res.insert(*did, file);
        }
        for (did, fun_def) in &self.fun_deps.fun_defs {
            let file = LeanFile::Fun(fun_def.name);
            res.insert(*did, file);
        }
        res
    }

    fn sort_files(&self) -> FxHashMap<fixpoint::DataSort, LeanFile> {
        let mut res = FxHashMap::default();
        for sort in &self.sort_deps.opaque_sorts {
            let data_sort = sort.name.clone();
            let file = LeanFile::OpaqueSort(data_sort.clone());
            res.insert(data_sort, file);
        }
        for data_decl in &self.sort_deps.data_decls {
            let data_sort = data_decl.name.clone();
            let file = LeanFile::Struct(data_sort.clone());
            res.insert(data_sort, file);
        }
        res
    }

    fn generate_lake_project_if_not_present(&self) -> Result<(), io::Error> {
        if !self.base.join(&self.project).exists() {
            Command::new("lake")
                .arg("new")
                .arg(&self.project)
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
        let name = &sort.name;
        let file = &LeanFile::OpaqueSort(name.clone());

        let path = self.path(file);
        if !path.exists() {
            let mut file = create_file_with_dirs(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "def {} := sorry", WithLeanCtxt { item: sort, cx: &cx })?;
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
        let name = &opaque_fun.name;
        let file = &LeanFile::OpaqueFun(*name);
        let path = self.path(file);
        if !path.exists() {
            let mut file = create_file_with_dirs(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            for dep in self.opaque_fun_dependencies(opaque_fun) {
                writeln!(file, "{}", self.import(dep))?;
            }
            writeln!(file, "def {} := sorry", self.var_name(name))?;
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
        let name = &data_decl.name;
        let file = &LeanFile::Struct(name.clone());
        let path = self.path(file);
        if !path.exists() {
            let mut file = create_file_with_dirs(path)?;
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.data_decl_dependencies(data_decl) {
                writeln!(file, "{}", self.import(dep))?;
            }
            // write data decl
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "{}", WithLeanCtxt { item: data_decl, cx: &cx })?;
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
        let name = &fun_def.name;
        let file = LeanFile::Fun(*name);
        let path = self.path(&file);
        if !path.exists() {
            let mut file = create_file_with_dirs(path)?;
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.fun_def_dependencies(did, fun_def) {
                writeln!(file, "{}", self.import(dep))?;
            }
            // write fun def
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "{}", WithLeanCtxt { item: fun_def, cx: &cx })?;
        }
        Ok(())
    }

    fn generate_lib_file_if_not_present(&self) -> Result<(), io::Error> {
        let path = self.path(&LeanFile::Fluxlib);
        if !path.exists() {
            let mut lib_file = create_file_with_dirs(path)?;
            writeln!(lib_file, "-- FLUX LIBRARY [DO NOT MODIFY] --")?;
            // TODO: Can't we write this from a single `write!` call?
            writeln!(
                lib_file,
                "def BitVec_shiftLeft {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)"
            )?;
            writeln!(
                lib_file,
                "def BitVec_ushiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)"
            )?;
            writeln!(
                lib_file,
                "def BitVec_sshiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)"
            )?;
            writeln!(
                lib_file,
                "def BitVec_uge {{ n : Nat }} (x y : BitVec n) := (BitVec.ult x y).not"
            )?;
            writeln!(
                lib_file,
                "def BitVec_sge {{ n : Nat }} (x y : BitVec n) := (BitVec.slt x y).not"
            )?;
            writeln!(
                lib_file,
                "def BitVec_ugt {{ n : Nat }} (x y : BitVec n) := (BitVec.ule x y).not"
            )?;
            writeln!(
                lib_file,
                "def BitVec_sgt {{ n : Nat }} (x y : BitVec n) := (BitVec.sle x y).not"
            )?;
            writeln!(
                lib_file,
                "def SmtMap (t0 t1 : Type) [Inhabited t0] [BEq t0] [Inhabited t1] : Type := t0 -> t1"
            )?;
            writeln!(
                lib_file,
                "def SmtMap_default {{ t0 t1: Type }} (v : t1) [Inhabited t0] [BEq t0] [Inhabited t1] : SmtMap t0 t1 := fun _ => v"
            )?;
            writeln!(
                lib_file,
                "def SmtMap_store {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) (v : t1) : SmtMap t0 t1 :=\n  fun x => if x == k then v else m x"
            )?;
            writeln!(
                lib_file,
                "def SmtMap_select {{ t0 t1 : Type }} [Inhabited t0] [BEq t0] [Inhabited t1] (m : SmtMap t0 t1) (k : t0) := m k"
            )?;
        }
        Ok(())
    }

    fn generate_vc_prelude(&self) -> Result<(), io::Error> {
        // 1. Generate lake project and lib file
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file_if_not_present()?;

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
            writeln!(file, "{}", self.import(&LeanFile::OpaqueSort(sort.name.clone())))?;
        }

        for data_decl in &self.sort_deps.data_decls {
            writeln!(file, "{}", self.import(&LeanFile::OpaqueSort(data_decl.name.clone())))?;
        }

        for (_, opaque_fun) in &self.fun_deps.opaque_funs {
            writeln!(file, "{}", self.import(&LeanFile::OpaqueFun(opaque_fun.name)))?;
        }

        for (_, fun_def) in &self.fun_deps.fun_defs {
            writeln!(file, "{}", self.import(&LeanFile::Fun(fun_def.name)))?;
        }

        Ok(())
    }

    fn generate_vc_file(&self) -> Result<(), io::Error> {
        // 1. Generate imports
        self.generate_vc_prelude()?;

        // 2. Create file and add imports
        let path = self.path(&LeanFile::VC);
        let mut file = create_file_with_dirs(path)?;
        self.generate_vc_imports(&mut file)?;

        // 3. Write the VC
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        writeln!(
            file,
            "def {} := {}",
            self.vc_name(),
            WithLeanCtxt {
                item: lean_format::LeanKConstraint {
                    kvars: &self.kvar_decls,
                    constr: &self.constraint
                },
                cx: &cx
            }
        )
    }

    fn generate_proof_file_if_not_present(&self) -> Result<(), io::Error> {
        let vc_name = self.vc_name();
        let proof_name = format!("{vc_name}_proof");
        let path = self.path(&LeanFile::Proof);

        if let Some(span) = self.genv.proven_externally(self.def_id.local_id()) {
            let dst_span = SpanTrace::from_path(&path, 3, 5, proof_name.len());
            println!("TRACE: hyperlinking proof {proof_name} to {span:?}");
            dbg::hyperlink_json!(self.genv.tcx(), span, dst_span);
        }

        if !path.exists() {
            let mut file = create_file_with_dirs(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            writeln!(file, "{}", self.import(&LeanFile::VC))?;
            writeln!(file, "def {proof_name} : {vc_name} := by")?;
            writeln!(file, "  unfold {vc_name}")?;
            writeln!(file, "  sorry")?;
        }
        Ok(())
    }

    pub fn encode_constraint(&self) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file_if_not_present()?;
        self.generate_vc_file()?;
        self.generate_proof_file_if_not_present()?;
        Ok(())
    }

    fn check_proof_help(&self, theorem_name: &str) -> io::Result<()> {
        let proof_name = format!("{theorem_name}_proof");
        let project_path = self.base.join(&self.project);
        let proof_path = format!(
            "{}/{}.lean",
            snake_case_to_pascal_case(&self.project),
            snake_case_to_pascal_case(&proof_name)
        );
        let child = Command::new("lake")
            .arg("--quiet")
            .arg("lean")
            .arg(proof_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .current_dir(project_path.as_path())
            .spawn()?;
        let out = child.wait_with_output()?;
        if out.stderr.is_empty() && out.stdout.is_empty() {
            Ok(())
        } else {
            let stderr = std::str::from_utf8(&out.stderr)
                .unwrap_or("Lean exited with a non-zero return code");
            Err(io::Error::other(stderr))
        }
    }

    pub fn check_proof(&self, def_id: MaybeExternId) -> QueryResult<()> {
        let theorem_name = self
            .genv
            .tcx()
            .def_path(def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_");
        self.check_proof_help(&theorem_name).map_err(|_| {
            let msg = format!("checking proof for {theorem_name} failed");
            let span = self.genv.tcx().def_span(def_id.resolved_id());
            QueryErr::Emitted(
                self.genv
                    .sess()
                    .dcx()
                    .handle()
                    .struct_span_err(span, msg)
                    .emit(),
            )
        })
    }
}
