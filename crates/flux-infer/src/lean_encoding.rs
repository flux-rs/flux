use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
    process::{Command, Stdio},
};

use flux_common::{dbg, dbg::SpanTrace};
use flux_config as config;
use flux_middle::{
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::PrettyMap,
};
use rustc_hash::FxHashSet;

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
    OpaqueSort(String),
    /// (machine) sorts generated from flux definitions
    Struct(String),
    /// (human) opaque flux functions, to be defined by the user in Lean
    OpaqueFun(String),
    /// (machine) functions generated from flux definitions
    Fun(String),
    /// (machine) propositions holding the Flux VCs
    VC(String),
    /// (human) interactively written proofs of flux VCs
    Proof(String),
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

impl LeanFile {
    fn segments(&self, project: &str) -> Vec<String> {
        let pascal_project_name = snake_case_to_pascal_case(project);
        match self {
            LeanFile::Fluxlib => {
                vec![pascal_project_name, "Lib".to_string()]
            }
            LeanFile::OpaqueSort(name) => {
                vec![
                    pascal_project_name,
                    "OpaqueSorts".to_string(),
                    snake_case_to_pascal_case(&name),
                ]
            }
            LeanFile::Struct(name) => {
                vec![pascal_project_name, "Structs".to_string(), snake_case_to_pascal_case(&name)]
            }
            LeanFile::OpaqueFun(name) => {
                vec![
                    pascal_project_name,
                    "OpaqueFuncs".to_string(),
                    snake_case_to_pascal_case(&name),
                ]
            }
            LeanFile::Fun(name) => {
                vec![pascal_project_name, "Funcs".to_string(), snake_case_to_pascal_case(&name)]
            }
            LeanFile::VC(name) => {
                vec![
                    pascal_project_name,
                    "Constraints".to_string(),
                    snake_case_to_pascal_case(&name),
                ]
            }
            LeanFile::Proof(name) => {
                vec![pascal_project_name, "Proofs".to_string(), snake_case_to_pascal_case(&name)]
            }
        }
    }

    fn import(&self, project: &str) -> String {
        format!("import {}\n", self.segments(project).join("."))
    }

    /// All paths should be generated here
    fn path(&self, base: &PathBuf, project: &str) -> PathBuf {
        let segments = self.segments(project);
        let mut path = base.join(project);
        for segment in segments {
            path = path.join(segment);
        }
        path.set_extension("lean");
        path
    }
}

pub struct LeanEncoder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    def_id: MaybeExternId,
    base: PathBuf,
    project: String,
    defs_file_name: String,
    pretty_var_map: PrettyMap<fixpoint::LocalVar>,
    opaque_sorts: Vec<fixpoint::SortDecl>,
    data_decls: Vec<fixpoint::DataDecl>,
    opaque_funs: Vec<fixpoint::ConstDecl>,
    fun_defs: Vec<fixpoint::FunDef>,
    kvar_decls: Vec<fixpoint::KVarDecl>,
    constraint: fixpoint::Constraint,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        def_id: MaybeExternId,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
        opaque_sorts: Vec<fixpoint::SortDecl>,
        structs: Vec<fixpoint::DataDecl>,
        opaque_funs: Vec<fixpoint::ConstDecl>,
        funs: Vec<fixpoint::FunDef>,
        kvar_decls: Vec<fixpoint::KVarDecl>,
        constraint: fixpoint::Constraint,
    ) -> Self {
        let defs_file_name = "Defs".to_string();
        let path = genv
            .tcx()
            .sess
            .opts
            .working_dir
            .local_path_if_available()
            .to_path_buf()
            .join(config::lean_dir());
        let project = config::lean_project().to_string();
        Self {
            genv,
            def_id,
            base: path,
            project,
            defs_file_name,
            pretty_var_map,
            opaque_sorts,
            data_decls: structs,
            opaque_funs,
            fun_defs: funs,
            kvar_decls,
            constraint,
        }
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

    fn path(&self, file: LeanFile) -> PathBuf {
        file.path(&self.base, &self.project)
    }

    fn import(&self, file: LeanFile) -> String {
        file.import(&self.project)
    }

    fn generate_opaque_sort_file_if_not_present(
        &self,
        sort: &fixpoint::SortDecl,
    ) -> Result<(), io::Error> {
        let name = format!("{}", LeanSortVar(&sort.name));
        let path = self.path(LeanFile::OpaqueSort(name.clone()));
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "def {} := sorry", WithLeanCtxt { item: sort, cx: &cx })?;
        }
        Ok(())
    }

    fn opaque_fun_dependencies(&self, opaque_fun: &fixpoint::ConstDecl) -> Vec<LeanFile> {
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
        todo!()
    }

    fn generate_opaque_fun_file_if_not_present(
        &self,
        opaque_fun: &fixpoint::ConstDecl,
    ) -> Result<(), io::Error> {
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        let name = format!("{}", WithLeanCtxt { item: &opaque_fun.name, cx: &cx });
        let path = self.path(LeanFile::OpaqueFun(name.clone()));
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
            for dep in self.opaque_fun_dependencies(opaque_fun) {
                writeln!(file, "{}", self.import(dep))?;
            }
            let name = format!("{}", WithLeanCtxt { item: &opaque_fun.name, cx: &cx });
            writeln!(file, "def {} := sorry", name)?;
        }
        Ok(())
    }

    fn data_decl_dependencies(&self, data_decl: &fixpoint::DataDecl) -> Vec<LeanFile> {
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
        let name = format!("{}", LeanSortVar(&data_decl.name));
        let path = self.path(LeanFile::Struct(name.clone()));
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            // import prelude
            writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
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

    fn fun_def_dependencies(&self, fun_def: &fixpoint::FunDef) -> Vec<LeanFile> {
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
        fun_def: &fixpoint::FunDef,
    ) -> Result<(), io::Error> {
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        let name = format!("{}", WithLeanCtxt { item: &fun_def.name, cx: &cx });
        let path = self.path(LeanFile::Fun(name.clone()));
        if !path.exists() {
            let mut file = fs::File::create(path)?;
            // import prelude
            writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
            // import sort dependencies
            for dep in self.fun_def_dependencies(fun_def) {
                writeln!(file, "{}", self.import(dep))?;
            }
            // write fun def
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(file, "{}", WithLeanCtxt { item: fun_def, cx: &cx })?;
        }
        Ok(())
    }

    fn generate_lib_file_if_not_present(&self) -> Result<(), io::Error> {
        let lib_path = self.path(LeanFile::Fluxlib);
        if lib_path.exists() {
            return Ok(());
        }
        let mut lib_file = fs::File::create(lib_path)?;
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
        for fun_def in &self.fun_defs {
            self.generate_fun_def_file_if_not_present(fun_def)?;
        }
        Ok(())
    }

    fn generate_vc_imports(&self, file: &mut fs::File) -> io::Result<()> {
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
        // // directly import the UIF/opaque constants used in the VC
        // for item in uif_consts {
        //     let fun_name = format!("{}", WithLeanCtxt { item, cx: &cx });
        //     let pascal_fun_file_name = snake_case_to_pascal_case(&fun_name);
        //     writeln!(file, "import {pascal_project_name}.{pascal_fun_file_name}")?;
        // }
        todo!();
        Ok(())
    }

    fn generate_vc_file(
        &self,
        // opaque_sorts: &[fixpoint::SortDecl],
        // opaque_funs: &[fixpoint::ConstDecl],
        // data_decls: &[fixpoint::DataDecl],
        // fun_defs: &[fixpoint::FunDef],
        // kvars: &[fixpoint::KVarDecl],
        // cstr: &fixpoint::Constraint,
    ) -> Result<(), io::Error> {
        // 1. Generate imports
        self.generate_vc_prelude()?;

        let name = self.vc_name();
        // 2. Create file and add imports
        let path = self.path(LeanFile::VC(name.to_string()));
        let mut file = fs::File::create(path)?;
        self.generate_vc_imports(&mut file)?;

        // 3. Write the VC
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        writeln!(
            file,
            "def {} := {}",
            name.replace(".", "_"),
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
        let path = self.path(LeanFile::Proof(proof_name.clone()));

        if let Some(span) = self.genv.proven_externally(self.def_id.local_id()) {
            let dst_span = SpanTrace::from_path(&path, 3, 5, proof_name.len());
            dbg::hyperlink_json!(self.genv.tcx(), span, dst_span);
        }

        if !path.exists() {
            let mut file = fs::File::create(path)?;
            writeln!(file, "{}", self.import(LeanFile::Fluxlib))?;
            writeln!(file, "{}", self.import(LeanFile::VC(vc_name.clone())))?;
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
