use std::{
    fs,
    io::{self, Write},
    path::Path,
    process::{Command, Stdio},
};

use flux_middle::{
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
};

use crate::{
    fixpoint_encoding::fixpoint,
    lean_format::{self, LeanConstDecl, LeanSortDecl, LeanSortVar, LeanVar},
};

pub struct LeanEncoder<'genv, 'tcx, 'a> {
    genv: GlobalEnv<'genv, 'tcx>,
    lean_path: &'a Path,
    project_name: String,
    defs_file_name: String,
}

impl<'genv, 'tcx, 'a> LeanEncoder<'genv, 'tcx, 'a> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        lean_path: &'a Path,
        project_name: String,
        defs_file_name: String,
    ) -> Self {
        Self { genv, lean_path, project_name, defs_file_name }
    }

    fn generate_lake_project_if_not_present(&self) -> Result<(), io::Error> {
        if !self.lean_path.join(self.project_name.as_str()).exists() {
            Command::new("lake")
                .arg("new")
                .arg(self.project_name.as_str())
                .arg("lib")
                .spawn()
                .and_then(|mut child| child.wait())
                .map(|_| ())
        } else {
            Ok(())
        }
    }

    fn generate_instance_file_if_not_present(
        &self,
        sorts: &[fixpoint::SortDecl],
        funs: &[fixpoint::ConstDecl],
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let instance_path = self.lean_path.join(
            format!("{}/{}/Instance.lean", self.project_name, pascal_project_name.as_str(),)
                .as_str(),
        );
        if !instance_path.exists() {
            let mut instance_file = fs::File::create(instance_path)?;
            writeln!(instance_file, "import {}.Lib", pascal_project_name.as_str())?;
            writeln!(instance_file, "import {}.OpaqueFluxDefs\n", pascal_project_name.as_str())?;
            writeln!(instance_file, "instance : FluxDefs where")?;
            for sort in sorts {
                writeln!(instance_file, "  {} := sorry", LeanSortVar(&sort.name))?;
            }
            for fun in funs {
                writeln!(instance_file, "  {} := sorry", LeanVar(&fun.name, self.genv))?;
            }
        }
        Ok(())
    }

    fn generate_inferred_instance_file(
        &self,
        sorts: &[fixpoint::SortDecl],
        funs: &[fixpoint::ConstDecl],
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let mut inferred_instance_file = fs::File::create(self.lean_path.join(format!(
            "{}/{}/InferredInstance.lean",
            self.project_name,
            pascal_project_name.as_str()
        )))?;
        writeln!(inferred_instance_file, "import {}.Instance\n", pascal_project_name.as_str())?;
        writeln!(inferred_instance_file, "def fluxDefsInstance : FluxDefs := inferInstance\n")?;
        for sort in sorts {
            writeln!(
                inferred_instance_file,
                "def {} := fluxDefsInstance.{}",
                LeanSortVar(&sort.name),
                LeanSortVar(&sort.name)
            )?;
        }
        for fun in funs {
            writeln!(
                inferred_instance_file,
                "def {} := fluxDefsInstance.{}",
                LeanConstDecl(fun, self.genv),
                LeanVar(&fun.name, self.genv)
            )?;
        }
        Ok(())
    }

    fn generate_typeclass_file(
        &self,
        sorts: &[fixpoint::SortDecl],
        funs: &[fixpoint::ConstDecl],
        data_decls: &[fixpoint::DataDecl],
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let mut opaque_defs_file = fs::File::create(self.lean_path.join(format!(
            "{}/{}/OpaqueFluxDefs.lean",
            self.project_name,
            pascal_project_name.as_str(),
        )))?;
        writeln!(opaque_defs_file, "import {}.Lib", pascal_project_name.as_str())?;
        if !data_decls.is_empty() {
            writeln!(opaque_defs_file, "-- STRUCT DECLS --")?;
            writeln!(opaque_defs_file, "mutual")?;
            for data_decl in data_decls {
                writeln!(opaque_defs_file, "{}", lean_format::LeanDataDecl(data_decl, self.genv))?;
            }
            writeln!(opaque_defs_file, "end")?;
        }
        writeln!(opaque_defs_file, "-- OPAQUE DEFS --")?;
        writeln!(opaque_defs_file, "class FluxDefs where")?;
        for sort in sorts {
            writeln!(opaque_defs_file, "  {}", LeanSortDecl(sort, self.genv))?;
        }
        for fun in funs {
            writeln!(opaque_defs_file, "  {}", LeanConstDecl(fun, self.genv))?;
        }
        self.generate_instance_file_if_not_present(sorts, funs)?;
        self.generate_inferred_instance_file(sorts, funs)?;
        Ok(())
    }

    fn generate_defs_file(
        &self,
        func_defs: &[fixpoint::FunDef],
        has_opaques: bool,
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let defs_path = self.lean_path.join(
            format!(
                "{}/{}/{}.lean",
                self.project_name,
                pascal_project_name.as_str(),
                self.defs_file_name
            )
            .as_str(),
        );
        let mut file = fs::File::create(defs_path)?;

        writeln!(file, "import {}.Lib", pascal_project_name.as_str())?;
        if has_opaques {
            writeln!(file, "import {}.InferredInstance", pascal_project_name.as_str())?;
        }
        if !func_defs.is_empty() {
            writeln!(file, "-- FUNC DECLS --")?;
            writeln!(file, "mutual")?;
            for fun_def in func_defs {
                writeln!(file, "{}", lean_format::LeanFunDef(fun_def, self.genv))?;
            }
            writeln!(file, "end")?;
        }
        Ok(())
    }

    fn generate_lib_file(&self) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let mut lib_file = fs::File::create(self.lean_path.join(format!(
            "{}/{}/Lib.lean",
            self.project_name,
            pascal_project_name.as_str()
        ).as_str()))?;
        writeln!(lib_file, "def BitVec_shiftLeft {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.shiftLeft x (s.toNat)")?;
        writeln!(lib_file, "def BitVec_ushiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.ushiftRight x (s.toNat)")?;
        writeln!(lib_file, "def BitVec_sshiftRight {{ n : Nat }} (x s : BitVec n) : BitVec n := BitVec.sshiftRight x (s.toNat)")?;
        writeln!(lib_file, "def BitVec_uge {{ n : Nat }} (x y : BitVec n) := (BitVec.ult x y).not")?;
        writeln!(lib_file, "def BitVec_sge {{ n : Nat }} (x y : BitVec n) := (BitVec.slt x y).not")?;
        writeln!(lib_file, "def BitVec_ugt {{ n : Nat }} (x y : BitVec n) := (BitVec.ule x y).not")?;
        writeln!(lib_file, "def BitVec_sgt {{ n : Nat }} (x y : BitVec n) := (BitVec.sle x y).not")?;
        writeln!(lib_file, "def SmtMap (Key Val : Type) [Inhabited Key] [BEq Key] [Inhabited Val] : Type := Key -> Val")?;
        writeln!(lib_file, "def SmtMapDefault {{ Key Val: Type }} (v : Val) [Inhabited Key] [BEq Key] [Inhabited Val] : SmtMap Key Val := fun _ => v")?;
        writeln!(lib_file, "def SmtMapStore {{ Key Val : Type }} [Inhabited Key] [BEq Key] [Inhabited Val] (m : SmtMap Key Val) (k : Key) (v : Val) : SmtMap Key Val :=\n  fun x => if x == k then v else m x")?;
        writeln!(lib_file, "def SmtMapSelect {{ Key Val : Type }} [Inhabited Key] [BEq Key] [Inhabited Val] (m : SmtMap Key Val) (k : Key) := m k")?;
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
        let has_opaques = !opaque_sorts.is_empty() || !opaque_funs.is_empty() || !data_decls.is_empty();
        if has_opaques {
            self.generate_typeclass_file(opaque_sorts, opaque_funs, data_decls)?;
        }
        if !func_defs.is_empty() {
            self.generate_defs_file(func_defs, has_opaques)?;
        }
        Ok(())
    }

    fn generate_theorem_file(
        &self,
        theorem_name: &str,
        cstr: &fixpoint::Constraint,
    ) -> Result<(), io::Error> {
        let pascal_project_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let theorem_path = self.lean_path.join(
            format!(
                "{}/{}/{}.lean",
                self.project_name,
                pascal_project_name.as_str(),
                Self::snake_case_to_pascal_case(theorem_name)
            )
            .as_str(),
        );
        let mut theorem_file = fs::File::create(theorem_path)?;
        writeln!(
            theorem_file,
            "import {}.Lib",
            pascal_project_name.as_str()
        )?;
        writeln!(
            theorem_file,
            "import {}.{}",
            pascal_project_name.as_str(),
            self.defs_file_name.as_str()
        )?;
        writeln!(theorem_file, "import {}.InferredInstance", pascal_project_name.as_str())?;
        writeln!(
            theorem_file,
            "def {} := {}",
            theorem_name.replace(".", "_"),
            lean_format::LeanConstraint(cstr, self.genv)
        )
    }

    fn generate_proof_file_if_not_present(&self, theorem_name: &str) -> Result<(), io::Error> {
        let module_name = Self::snake_case_to_pascal_case(self.project_name.as_str());
        let proof_name = format!("{theorem_name}_proof");
        let proof_path = self.lean_path.join(
            format!(
                "{}/{}/{}.lean",
                self.project_name.as_str(),
                module_name.as_str(),
                Self::snake_case_to_pascal_case(proof_name.as_str())
            )
            .as_str(),
        );
        if proof_path.exists() {
            return Ok(());
        }
        let mut proof_file = fs::File::create(proof_path)?;
        writeln!(
            proof_file,
            "import {}.Lib",
            module_name.as_str()
        )?;
        writeln!(
            proof_file,
            "import {}.{}",
            module_name.as_str(),
            Self::snake_case_to_pascal_case(theorem_name)
        )?;
        writeln!(proof_file, "def {proof_name} : {theorem_name} := by")?;
        writeln!(proof_file, "  unfold {theorem_name}")?;
        writeln!(proof_file, "  sorry")
    }

    pub fn encode_constraint(
        &self,
        def_id: MaybeExternId,
        cstr: &fixpoint::Constraint,
    ) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        self.generate_lib_file()?;
        let theorem_name = self
            .genv
            .tcx()
            .def_path(def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_");
        self.generate_theorem_file(theorem_name.as_str(), cstr)?;
        self.generate_proof_file_if_not_present(theorem_name.as_str())
    }

    fn check_proof_help(&self, theorem_name: &str) -> io::Result<()> {
        let proof_name = format!("{theorem_name}_proof");
        let project_path = self.lean_path.join(self.project_name.as_str());
        let proof_path = project_path.join(format!(
            "{}/{}.lean",
            Self::snake_case_to_pascal_case(self.project_name.as_str()),
            Self::snake_case_to_pascal_case(proof_name.as_str())
        ));
        let child = Command::new("lake")
            .arg("--dir")
            .arg(project_path.to_str().unwrap())
            .arg("lean")
            .arg(proof_path.to_str().unwrap())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
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
        self.check_proof_help(theorem_name.as_str()).map_err(|_| {
            let msg = format!("checking proof for {} failed", theorem_name.as_str());
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
