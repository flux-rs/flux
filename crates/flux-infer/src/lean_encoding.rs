use std::{
    collections::HashMap,
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

use crate::{
    fixpoint_encoding::{FixpointSolution, fixpoint},
    lean_format::{self, LeanCtxt, LeanSortVar, WithLeanCtxt},
};

pub struct LeanEncoder<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    path: PathBuf,
    project: String,
    defs_file_name: String,
    pretty_var_map: PrettyMap<fixpoint::LocalVar>,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        pretty_var_map: PrettyMap<fixpoint::LocalVar>,
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
        Self { genv, path, project, defs_file_name, pretty_var_map }
    }

    fn generate_lake_project_if_not_present(&self) -> Result<(), io::Error> {
        if !self.path.join(&self.project).exists() {
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

    fn generate_sort_def_file_if_not_present(
        &self,
        sort: &fixpoint::SortDecl,
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let pascal_sort_file_name =
            Self::snake_case_to_pascal_case(&format!("{}", LeanSortVar(&sort.name)));
        let instance_path = self
            .path
            .join(format!("{}/{pascal_project_name}/{pascal_sort_file_name}.lean", self.project));
        if !instance_path.exists() {
            let mut instance_file = fs::File::create(instance_path)?;
            writeln!(instance_file, "import {}.Lib\n", pascal_project_name)?;
            let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
            writeln!(instance_file, "def {} := sorry", WithLeanCtxt { item: sort, cx: &cx })?;
        }
        Ok(())
    }

    fn generate_func_def_file_if_not_present(
        &self,
        fun: &fixpoint::ConstDecl,
        has_opaque_sorts: bool,
        has_data_decls: bool,
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        let fun_name = format!("{}", WithLeanCtxt { item: &fun.name, cx: &cx });
        let pascal_fun_file_name = Self::snake_case_to_pascal_case(&fun_name);
        let instance_path = self
            .path
            .join(format!("{}/{pascal_project_name}/{pascal_fun_file_name}.lean", self.project));
        if !instance_path.exists() {
            let mut instance_file = fs::File::create(instance_path)?;
            writeln!(instance_file, "import {pascal_project_name}.Lib")?;
            if has_opaque_sorts {
                writeln!(instance_file, "import {pascal_project_name}.OpaqueSorts")?;
            }
            if has_data_decls {
                writeln!(instance_file, "import {pascal_project_name}.Structs")?;
            }
            writeln!(instance_file, "def {} := sorry", WithLeanCtxt { item: fun, cx: &cx })?;
        }
        Ok(())
    }

    fn generate_opaque_sort_files(&self, sorts: &[fixpoint::SortDecl]) -> Result<(), io::Error> {
        if sorts.is_empty() {
            return Ok(());
        }
        for sort in sorts {
            self.generate_sort_def_file_if_not_present(sort)?;
        }
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let mut opaque_sorts_file = fs::File::create(
            self.path
                .join(format!("{}/{pascal_project_name}/OpaqueSorts.lean", self.project)),
        )?;
        for sort in sorts {
            let pascal_sort_file_name =
                Self::snake_case_to_pascal_case(&format!("{}", LeanSortVar(&sort.name)));
            writeln!(opaque_sorts_file, "import {pascal_project_name}.{pascal_sort_file_name}")?;
        }
        Ok(())
    }

    fn generate_struct_defs_file(
        &self,
        data_decls: &[fixpoint::DataDecl],
        has_opaque_sorts: bool,
    ) -> Result<(), io::Error> {
        if data_decls.is_empty() {
            return Ok(());
        }
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let mut structs_file = fs::File::create(
            self.path
                .join(format!("{}/{}/Structs.lean", self.project, pascal_project_name,)),
        )?;
        writeln!(structs_file, "import {}.Lib", pascal_project_name)?;
        if has_opaque_sorts {
            writeln!(structs_file, "import {}.OpaqueSorts", pascal_project_name)?;
        }
        writeln!(structs_file, "-- STRUCT DECLS --")?;
        writeln!(structs_file, "mutual")?;
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        for data_decl in data_decls {
            writeln!(structs_file, "{}", WithLeanCtxt { item: data_decl, cx: &cx })?;
        }
        writeln!(structs_file, "end")?;
        Ok(())
    }

    fn generate_opaque_func_files(
        &self,
        funs: &[fixpoint::ConstDecl],
        has_opaque_sorts: bool,
        has_data_decls: bool,
    ) -> Result<(), io::Error> {
        if funs.is_empty() {
            return Ok(());
        }
        for fun in funs {
            self.generate_func_def_file_if_not_present(fun, has_opaque_sorts, has_data_decls)?;
        }
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let mut opaque_funcs_file = fs::File::create(
            self.path
                .join(format!("{}/{pascal_project_name}/OpaqueFuncs.lean", self.project)),
        )?;
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        for fun in funs {
            let fun_name = format!("{}", WithLeanCtxt { item: &fun.name, cx: &cx });
            let pascal_fun_file_name = Self::snake_case_to_pascal_case(&fun_name);
            writeln!(opaque_funcs_file, "import {pascal_project_name}.{pascal_fun_file_name}")?;
        }
        Ok(())
    }

    fn generate_func_defs_file(
        &self,
        func_defs: &[fixpoint::FunDef],
        has_opaque_sorts: bool,
        has_data_decls: bool,
        has_opaque_funcs: bool,
    ) -> Result<(), io::Error> {
        if func_defs.is_empty() {
            return Ok(());
        }
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let defs_path = self
            .path
            .join(format!("{}/{pascal_project_name}/{}.lean", self.project, self.defs_file_name));
        let mut file = fs::File::create(defs_path)?;

        writeln!(file, "import {pascal_project_name}.Lib")?;
        if has_opaque_sorts {
            writeln!(file, "import {pascal_project_name}.OpaqueSorts")?;
        }
        if has_data_decls {
            writeln!(file, "import {pascal_project_name}.Structs")?;
        }
        if has_opaque_funcs {
            writeln!(file, "import {pascal_project_name}.OpaqueFuncs")?;
        }
        writeln!(file, "-- FUNC DECLS --")?;
        writeln!(file, "mutual")?;
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        for fun_def in func_defs {
            writeln!(file, "{}", WithLeanCtxt { item: fun_def, cx: &cx })?;
        }
        writeln!(file, "end")?;
        Ok(())
    }

    fn generate_lib_file(&self) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let mut lib_file = fs::File::create(
            self.path
                .join(format!("{}/{pascal_project_name}/Lib.lean", self.project)),
        )?;
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

    pub fn encode_defs(
        &self,
        opaque_sorts: &[fixpoint::SortDecl],
        opaque_funs: &[fixpoint::ConstDecl],
        data_decls: &[fixpoint::DataDecl],
        func_defs: &[fixpoint::FunDef],
    ) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file()?;

        let has_opaque_sorts = !opaque_sorts.is_empty();
        let has_data_decls = !data_decls.is_empty();
        let has_opaque_funcs = !opaque_funs.is_empty();

        self.generate_opaque_sort_files(opaque_sorts)?;
        self.generate_struct_defs_file(data_decls, has_opaque_sorts)?;
        self.generate_opaque_func_files(opaque_funs, has_opaque_sorts, has_data_decls)?;
        self.generate_func_defs_file(
            func_defs,
            has_opaque_sorts,
            has_data_decls,
            has_opaque_funcs,
        )?;
        Ok(())
    }

    fn theorem_path(&self, theorem_name: &str) -> PathBuf {
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);

        self.path.join(format!(
            "{}/{}/{}.lean",
            self.project,
            pascal_project_name,
            Self::snake_case_to_pascal_case(theorem_name)
        ))
    }

    fn generate_theorem_file(
        &self,
        theorem_name: &str,
        kvars: &[fixpoint::KVarDecl],
        cstr: &fixpoint::Constraint,
        kvar_solutions: HashMap<fixpoint::KVid, FixpointSolution>,
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(&self.project);
        let theorem_path = self.theorem_path(theorem_name);
        let mut theorem_file = fs::File::create(theorem_path)?;
        writeln!(theorem_file, "import {}.Lib", pascal_project_name)?;
        if self
            .path
            .join(format!("{}/{pascal_project_name}/{}.lean", self.project, self.defs_file_name))
            .exists()
        {
            writeln!(theorem_file, "import {pascal_project_name}.{}", self.defs_file_name)?;
        }
        if self
            .path
            .join(format!("{}/{pascal_project_name}/OpaqueSorts.lean", self.project))
            .exists()
        {
            writeln!(theorem_file, "import {pascal_project_name}.OpaqueSorts")?;
        }
        if self
            .path
            .join(format!("{}/{pascal_project_name}/OpaqueFuncs.lean", self.project))
            .exists()
        {
            writeln!(theorem_file, "import {pascal_project_name}.OpaqueFuncs")?;
        }
        let cx = LeanCtxt { genv: self.genv, pretty_var_map: &self.pretty_var_map };
        writeln!(
            theorem_file,
            "{}",
            WithLeanCtxt {
                item: lean_format::LeanKConstraint {
                    theorem_name,
                    kvars,
                    constr: cstr,
                    kvar_solutions
                },
                cx: &cx
            }
        )
    }

    fn generate_proof_file_if_not_present(
        &self,
        def_id: MaybeExternId,
        theorem_name: &str,
    ) -> Result<(), io::Error> {
        let module_name = Self::snake_case_to_pascal_case(&self.project);
        let proof_name = format!("{theorem_name}_proof");
        let proof_path = self.path.join(format!(
            "{}/{}/{}.lean",
            self.project,
            module_name,
            Self::snake_case_to_pascal_case(&proof_name)
        ));

        if let Some(span) = self.genv.proven_externally(def_id.local_id()) {
            let dst_span = SpanTrace::from_path(&proof_path, 3, 5, proof_name.len());
            dbg::hyperlink_json!(self.genv.tcx(), span, dst_span);
        }

        if proof_path.exists() {
            return Ok(());
        }
        let mut proof_file = fs::File::create(proof_path)?;
        writeln!(proof_file, "import {module_name}.Lib")?;
        writeln!(
            proof_file,
            "import {}.{}",
            module_name,
            Self::snake_case_to_pascal_case(theorem_name)
        )?;
        writeln!(proof_file, "def {proof_name} : {theorem_name} := by")?;
        writeln!(proof_file, "  unfold {theorem_name}")?;
        writeln!(proof_file, "  sorry")
    }

    pub fn encode_constraint(
        &self,
        def_id: MaybeExternId,
        kvars: &[fixpoint::KVarDecl],
        cstr: &fixpoint::Constraint,
        kvar_solutions: HashMap<fixpoint::KVid, FixpointSolution>,
    ) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file()?;
        let theorem_name = self
            .genv
            .tcx()
            .def_path(def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_");

        self.generate_theorem_file(&theorem_name, kvars, cstr, kvar_solutions)?;

        self.generate_proof_file_if_not_present(def_id, &theorem_name)
    }

    fn check_proof_help(&self, theorem_name: &str) -> io::Result<()> {
        let proof_name = format!("{theorem_name}_proof");
        let project_path = self.path.join(&self.project);
        let proof_path = format!(
            "{}/{}.lean",
            Self::snake_case_to_pascal_case(&self.project),
            Self::snake_case_to_pascal_case(&proof_name)
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
}
