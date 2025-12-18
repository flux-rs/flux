use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
    process::{Command, Stdio},
};

use flux_common::dbg::{self, SpanTrace};
use flux_config as config;
use flux_middle::{
    def_id::{FluxDefId, MaybeExternId},
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::PrettyMap,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    fixpoint_encoding::fixpoint,
    lean_format::{self, LeanCtxt, LeanSortVar, WithLeanCtxt},
};

/// Different kinds of Lean files
#[derive(Debug, Clone)]
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
    /// (machine) propositions holding the Flux VCs
    VC(MaybeExternId),
    /// (human) interactively written proofs of flux VCs
    Proof(MaybeExternId),
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
    opaque_sorts: Vec<fixpoint::SortDecl>,
    data_decls: Vec<fixpoint::DataDecl>,
    opaque_funs: Vec<fixpoint::ConstDecl>,
    fun_defs: Vec<(FluxDefId, fixpoint::FunDef)>,
    kvar_decls: Vec<fixpoint::KVarDecl>,
    constraint: fixpoint::Constraint,
    sort_files: FxHashMap<fixpoint::DataSort, LeanFile>,
    fun_files: FxHashMap<fixpoint::Var, LeanFile>,
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

    fn def_id_name(&self, def_id: &MaybeExternId) -> String {
        self.genv
            .tcx()
            .def_path(def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_")
    }

    fn segments(&self, file: &LeanFile) -> Vec<String> {
        let project_name = snake_case_to_pascal_case(&self.project);
        match file {
            LeanFile::Fluxlib => {
                vec![project_name, "Lib".to_string()]
            }
            LeanFile::OpaqueSort(sort) => {
                let name = self.datasort_name(&sort);
                vec![project_name, "OpaqueSorts".to_string(), name]
            }
            LeanFile::Struct(sort) => {
                let name = self.datasort_name(&sort);
                vec![project_name, "Structs".to_string(), name]
            }
            LeanFile::OpaqueFun(name) => {
                let name = self.var_name(&name);
                vec![project_name, "OpaqueFuncs".to_string(), name]
            }
            LeanFile::Fun(name) => {
                let name = self.var_name(&name);
                vec![project_name, "Funcs".to_string(), name]
            }
            LeanFile::VC(def_id) => {
                let name = self.def_id_name(def_id);
                vec![project_name, "Constraints".to_string(), name]
            }
            LeanFile::Proof(def_id) => {
                let name = self.def_id_name(def_id);
                vec![project_name, "Proofs".to_string(), name]
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
        opaque_sorts: Vec<fixpoint::SortDecl>,
        data_decls: Vec<fixpoint::DataDecl>,
        opaque_funs: Vec<fixpoint::ConstDecl>,
        fun_defs: Vec<(FluxDefId, fixpoint::FunDef)>,
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
            opaque_sorts,
            data_decls,
            opaque_funs,
            fun_defs,
            kvar_decls,
            constraint,
            fun_files: FxHashMap::default(),
            sort_files: FxHashMap::default(),
        };

        encoder.fun_files = encoder.fun_files();
        encoder.sort_files = encoder.sort_files();
        encoder
    }

    fn fun_files(&self) -> FxHashMap<fixpoint::Var, LeanFile> {
        let mut res = FxHashMap::default();
        for opaque_fun in &self.opaque_funs {
            let var = opaque_fun.name.clone();
            let file = LeanFile::OpaqueFun(var.clone());
            res.insert(var, file);
        }
        for (_, fun_def) in &self.fun_defs {
            let var = fun_def.name.clone();
            let file = LeanFile::Fun(var.clone());
            res.insert(var, file);
        }
        res
    }

    fn sort_files(&self) -> FxHashMap<fixpoint::DataSort, LeanFile> {
        let mut res = FxHashMap::default();
        for sort in &self.opaque_sorts {
            let data_sort = sort.name.clone();
            let file = LeanFile::OpaqueSort(data_sort.clone());
            res.insert(data_sort, file);
        }
        for data_decl in &self.data_decls {
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
                .map(|_| ())
        } else {
            Ok(())
        }
    }

    fn generate_opaque_sort_file_if_not_present(
        &self,
        sort: &fixpoint::SortDecl,
    ) -> Result<(), io::Error> {
        let name = &sort.name;
        let file = &LeanFile::OpaqueSort(name.clone());

        let path = self.path(file);
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "def {} := sorry", WithLeanCtxt { item: sort, cx: &cx })?;
        }
        Ok(())
    }

    fn opaque_fun_dependencies(&self, opaque_fun: &fixpoint::ConstDecl) -> Vec<LeanFile> {
        let name = &opaque_fun.name;
        // let mut acc = vec![];
        // data_decl.deps(&mut acc);
        // acc.into_iter()
        //     .map(|dep| {
        //         let name = format!("{}", LeanSortVar(&dep));
        //         if self.structs.contains(&dep) {
        //             LeanFile::Struct(name)
        //         } else {
        //             LeanFile::OpaqueSort(name)
        //         }
        //     })
        //     .collect()
        todo!("HEREHEREHEREHERE")
    }

    fn generate_opaque_fun_file_if_not_present(
        &self,
        opaque_fun: &fixpoint::ConstDecl,
    ) -> Result<(), io::Error> {
        let name = &opaque_fun.name;
        let file = &LeanFile::OpaqueFun(name.clone());
        let path = self.path(file);
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            for dep in self.opaque_fun_dependencies(opaque_fun) {
                writeln!(file, "{}", self.import(&dep))?;
            }
            writeln!(file, "def {} := sorry", self.var_name(name))?;
        }
        Ok(())
    }

    fn data_decl_dependencies(&self, data_decl: &fixpoint::DataDecl) -> Vec<LeanFile> {
        let name = &data_decl.name;

        todo!("DEPENDENCIES")
        // let mut acc = vec![];
        // data_decl.deps(&mut acc);
        // acc.into_iter()
        //     .map(|dep| {
        //         let name = format!("{}", LeanSortVar(&dep));
        //         if self.structs.contains(&dep) {
        //             LeanFile::Struct(name)
        //         } else {
        //             LeanFile::OpaqueSort(name)
        //         }
        //     })
        //     .collect()
    }

    fn generate_struct_file_if_not_present(
        &self,
        data_decl: &fixpoint::DataDecl,
    ) -> Result<(), io::Error> {
        let name = &data_decl.name;
        let file = &LeanFile::Struct(name.clone());
        let path = self.path(file);
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.data_decl_dependencies(data_decl) {
                writeln!(file, "{}", self.import(&dep))?;
            }
            // write data decl
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "{}", WithLeanCtxt { item: data_decl, cx: &cx })?;
        }
        Ok(())
    }

    fn fun_def_dependencies(&self, did: &FluxDefId) -> Vec<LeanFile> {
        // let mut acc = vec![];
        // fun_def.deps(&mut acc);
        // acc.into_iter()
        //     .map(|dep| {
        //         let name = format!("{}", LeanSortVar(&dep));
        //         if self.structs.contains(&dep) {
        //             LeanFile::Struct(name)
        //         } else {
        //             LeanFile::OpaqueSort(name)
        //         }
        //     })
        //     .collect()
        todo!("DEPENDENCIES")
    }

    fn generate_fun_def_file_if_not_present(
        &self,
        did: &FluxDefId,
        fun_def: &fixpoint::FunDef,
    ) -> Result<(), io::Error> {
        let name = &fun_def.name;
        let file = LeanFile::Fun(name.clone());
        let path = self.path(&file);
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            // import prelude
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.fun_def_dependencies(did) {
                writeln!(file, "{}", self.import(&dep))?;
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
            let mut lib_file = fs::File::create(path)?;
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
        for sort in &self.opaque_sorts {
            self.generate_opaque_sort_file_if_not_present(sort)?;
        }

        // 2. Generate Struct Files
        for data_decl in &self.data_decls {
            self.generate_struct_file_if_not_present(data_decl)?;
        }

        // 3. Generate Opaque Func Files
        for opaque_fun in &self.opaque_funs {
            self.generate_opaque_fun_file_if_not_present(opaque_fun)?;
        }

        // 4. Generate Func Def Files
        for (did, fun_def) in &self.fun_defs {
            self.generate_fun_def_file_if_not_present(did, fun_def)?;
        }
        Ok(())
    }

    fn generate_vc_imports(&self, file: &mut fs::File) -> io::Result<()> {
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
        // // directly import the UIF/opaque constants used in the VC
        // for item in uif_consts {
        //     let fun_name = format!("{}", WithLeanCtxt { item, cx: &cx });
        //     let pascal_fun_file_name = snake_case_to_pascal_case(&fun_name);
        //     writeln!(file, "import {pascal_project_name}.{pascal_fun_file_name}")?;
        // }
        todo!("DEPENDENCIES");
    }

    fn generate_vc_file(&self) -> Result<(), io::Error> {
        // 1. Generate imports
        self.generate_vc_prelude()?;

        let name = &self.def_id;
        let file = LeanFile::VC(*name);
        // 2. Create file and add imports
        let path = self.path(&file);
        let mut file = fs::File::create(path)?;
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
        let path = self.path(&LeanFile::Proof(self.def_id.clone()));

        if let Some(span) = self.genv.proven_externally(self.def_id.local_id()) {
            let dst_span = SpanTrace::from_path(&path, 3, 5, proof_name.len());
            dbg::hyperlink_json!(self.genv.tcx(), span, dst_span);
        }

        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(&LeanFile::Fluxlib))?;
            writeln!(file, "{}", self.import(&LeanFile::VC(self.def_id.clone())))?;
            writeln!(file, "def {proof_name} : {vc_name} := by")?;
            writeln!(file, "  unfold {vc_name}")?;
            writeln!(file, "  sorry")?;
        }
        return Ok(());
    }

    fn vc_name(&self) -> String {
        self.genv
            .tcx()
            .def_path(self.def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_")
    }

    pub fn encode_constraint(&self) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file_if_not_present()?;
        self.generate_vc_file()?;
        self.generate_proof_file_if_not_present()
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
