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
use itertools::Itertools;

use crate::{
    fixpoint_encoding::fixpoint,
    lean_format::{
        self, LeanConstDecl, LeanDataField, LeanSort, LeanSortDecl, LeanSortVar, LeanVar,
    },
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
    ) -> Result<(), io::Error> {
        let mut opaque_defs_file = fs::File::create(self.lean_path.join(format!(
            "{}/{}/OpaqueFluxDefs.lean",
            self.project_name,
            Self::snake_case_to_pascal_case(self.project_name.as_str()),
        )))?;
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
        data_decls: &[fixpoint::DataDecl],
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
        if has_opaques {
            writeln!(file, "import {}.InferredInstance", pascal_project_name.as_str())?;
        }
        let structs = data_decls
            .iter()
            .filter(|decl| decl.ctors.len() == 1)
            .collect_vec();
        if !data_decls.is_empty() {
            writeln!(file, "-- STRUCT DECLS --")?;
            writeln!(file, "mutual")?;
            for data_decl in data_decls {
                writeln!(file, "{}", lean_format::LeanDataDecl(data_decl, self.genv))?;
            }
            writeln!(file, "end")?;
        }
        if !structs.is_empty() {
            writeln!(file, "-- CONSTRUCTORS & Projections --")?;
            writeln!(file, "mutual")?;
            for struct_decl in &structs {
                writeln!(
                    file,
                    "def {} {} : {} := {{ {} }}",
                    LeanVar(&struct_decl.ctors[0].name, self.genv),
                    struct_decl.ctors[0]
                        .fields
                        .iter()
                        .map(|field| LeanDataField(field, self.genv))
                        .format(" "),
                    LeanSortVar(&struct_decl.name),
                    struct_decl.ctors[0]
                        .fields
                        .iter()
                        .map(|field| LeanVar(&field.name, self.genv))
                        .format(", "),
                )?;
            }
            for struct_decl in &structs {
                for field in &struct_decl.ctors[0].fields {
                    writeln!(
                        file,
                        "def {} (s : {}) : {} := {}.{} s",
                        LeanVar(&field.name, self.genv),
                        LeanSortVar(&struct_decl.name),
                        LeanSort(&field.sort),
                        LeanSortVar(&struct_decl.name),
                        LeanVar(&field.name, self.genv),
                    )?;
                }
            }
            writeln!(file, "end")?;
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

    pub fn encode_defs(
        &self,
        opaque_sorts: &[fixpoint::SortDecl],
        opaque_funs: &[fixpoint::ConstDecl],
        data_decls: &[fixpoint::DataDecl],
        func_defs: &[fixpoint::FunDef],
    ) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        let has_opaques = !opaque_sorts.is_empty() || !opaque_funs.is_empty();
        if has_opaques {
            self.generate_typeclass_file(opaque_sorts, opaque_funs)?;
        }
        if !data_decls.is_empty() || !func_defs.is_empty() {
            self.generate_defs_file(data_decls, func_defs, has_opaques)?;
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
