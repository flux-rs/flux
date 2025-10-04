use std::{
    fs,
    io::{self, Write},
    path,
    process::{Command, Stdio},
};

use flux_middle::{
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
};
use itertools::Itertools;
use liquid_fixpoint::Identifier;

use crate::fixpoint_encoding::fixpoint::{BinRel, ConstDecl, Constraint, Expr, FunDef, Pred};

pub(crate) struct ConstDef(pub ConstDecl, pub Option<Expr>);

pub(crate) struct LeanEncoder<'genv, 'tcx> {
    def_id: MaybeExternId,
    genv: GlobalEnv<'genv, 'tcx>,
    fun_defs: Vec<FunDef>,
    constants: Vec<ConstDef>,
    constraint: Constraint,
}

impl<'genv, 'tcx> LeanEncoder<'genv, 'tcx> {
    pub fn new(
        def_id: MaybeExternId,
        genv: GlobalEnv<'genv, 'tcx>,
        fun_defs: Vec<FunDef>,
        constants: Vec<ConstDecl>,
        constraint: Constraint,
    ) -> Self {
        let constants = Self::extract_const_defs(constants, &constraint);
        Self { def_id, genv, fun_defs, constants, constraint }
    }

    pub fn fun_defs(&self) -> &[FunDef] {
        &self.fun_defs
    }

    pub fn constraint(&self) -> &Constraint {
        &self.constraint
    }

    pub fn constants(&self) -> &[ConstDef] {
        &self.constants
    }

    pub(crate) fn theorem_name(&self) -> String {
        self.genv
            .tcx()
            .def_path(self.def_id.resolved_id())
            .to_filename_friendly_no_crate()
            .replace("-", "_")
    }

    fn proof_name(&self) -> String {
        format!("{}_proof", self.theorem_name()).to_string()
    }

    fn generate_lake_project_if_not_present(
        &self,
        lean_path: &path::Path,
        project_name: &str,
    ) -> Result<(), io::Error> {
        if !lean_path.join(project_name).exists() {
            Command::new("lake")
                .arg("new")
                .arg(project_name)
                .arg("lib")
                .spawn()
                .and_then(|mut child| child.wait())
                .map(|_| ())
        } else {
            Ok(())
        }
    }

    fn generate_def_file(
        &self,
        lean_path: &path::Path,
        project_name: &str,
    ) -> Result<(), io::Error> {
        self.generate_lake_project_if_not_present(lean_path, project_name)?;
        let theorem_path = lean_path.join(
            format!(
                "{project_name}/{}/{}.lean",
                Self::snake_case_to_pascal_case(project_name),
                Self::snake_case_to_pascal_case(self.theorem_name().as_str())
            )
            .as_str(),
        );
        let mut file = fs::File::create(theorem_path)?;
        writeln!(file, "{self}")
    }

    fn generate_proof_file_if_not_present(
        &self,
        lean_path: &path::Path,
        project_name: &str,
    ) -> Result<(), io::Error> {
        self.generate_def_file(lean_path, project_name)?;
        let module_name = Self::snake_case_to_pascal_case(project_name);
        let proof_name = self.proof_name();
        let proof_path = lean_path.join(
            format!(
                "{project_name}/{}/{}.lean",
                module_name.as_str(),
                Self::snake_case_to_pascal_case(proof_name.as_str())
            )
            .as_str(),
        );
        let theorem_name = self.theorem_name();
        if !proof_path.exists() {
            let mut file = std::fs::File::create(proof_path)?;
            writeln!(
                file,
                "import {}.{}",
                Self::snake_case_to_pascal_case(module_name.as_str()),
                Self::snake_case_to_pascal_case(theorem_name.as_str())
            )?;
            writeln!(file, "def {proof_name} : {theorem_name} := by")?;
            writeln!(file, "  unfold {theorem_name}")?;
            writeln!(file, "  sorry")
        } else {
            Ok(())
        }
    }

    fn check_proof_help(&self, lean_path: &path::Path, project_name: &str) -> std::io::Result<()> {
        self.generate_proof_file_if_not_present(lean_path, project_name)?;
        let project_path = lean_path.join(project_name);
        let proof_path = project_path.join(format!(
            "{}/{}.lean",
            Self::snake_case_to_pascal_case(project_name),
            Self::snake_case_to_pascal_case(self.proof_name().as_str())
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

    pub fn check_proof(&self, lean_path: &path::Path, project_name: &str) -> QueryResult<()> {
        self.check_proof_help(lean_path, project_name).map_err(|_| {
            let msg = format!("checking proof for {} failed", self.theorem_name());
            let span = self.genv.tcx().def_span(self.def_id.resolved_id());
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

    fn extract_const_defs(const_decls: Vec<ConstDecl>, constraint: &Constraint) -> Vec<ConstDef> {
        const_decls
            .into_iter()
            .map(|const_decl| {
                let mut defs = vec![];
                Self::extract_const_def(&const_decl, constraint, &mut defs);
                if defs.len() <= 1 {
                    ConstDef(const_decl, defs.pop())
                } else {
                    panic!("Constant {} has {} definitions", const_decl.name.display(), defs.len())
                }
            })
            .collect_vec()
    }

    fn extract_const_def(const_decl: &ConstDecl, constraint: &Constraint, acc: &mut Vec<Expr>) {
        match constraint {
            Constraint::ForAll(bind, inner) => {
                if let Pred::Expr(Expr::Atom(BinRel::Eq, equals)) = &bind.pred {
                    if let Expr::Var(vl) = &equals[0]
                        && vl.eq(&const_decl.name)
                    {
                        acc.push(equals[1].clone());
                    }
                    if let Expr::Var(vr) = &equals[1]
                        && vr.eq(&const_decl.name)
                    {
                        acc.push(equals[0].clone());
                    }
                    Self::extract_const_def(const_decl, inner.as_ref(), acc);
                }
            }
            Constraint::Conj(conjuncts) => {
                conjuncts
                    .iter()
                    .for_each(|constraint| Self::extract_const_def(const_decl, constraint, acc));
            }
            Constraint::Pred(..) => {}
        }
    }
}
