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

use crate::{fixpoint_encoding::fixpoint, lean_format};

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

    pub fn encode_defs(&self, defs: &[fixpoint::FunDef]) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present()?;
        let defs_path = self.lean_path.join(
            format!(
                "{}/{}/{}.lean",
                self.project_name,
                Self::snake_case_to_pascal_case(self.project_name.as_str()),
                self.defs_file_name
            )
            .as_str(),
        );
        let mut file = fs::File::create(defs_path)?;
        writeln!(file, "mutual")?;
        for fun_def in defs {
            writeln!(file, "{}", lean_format::LeanFunDef(fun_def, self.genv))?;
        }
        writeln!(file, "end")
    }

    fn generate_theorem_file(
        &self,
        theorem_name: &str,
        cstr: &fixpoint::Constraint,
    ) -> Result<(), io::Error> {
        let theorem_path = self.lean_path.join(
            format!(
                "{}/{}/{}.lean",
                self.project_name,
                Self::snake_case_to_pascal_case(self.project_name.as_str()),
                Self::snake_case_to_pascal_case(theorem_name)
            )
            .as_str(),
        );
        let mut theorem_file = fs::File::create(theorem_path)?;
        writeln!(
            theorem_file,
            "import {}.{}",
            Self::snake_case_to_pascal_case(self.project_name.as_str()),
            self.defs_file_name.as_str()
        )?;
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
            .to_filename_friendly_no_crate();
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
            .replace(".", "_");
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
