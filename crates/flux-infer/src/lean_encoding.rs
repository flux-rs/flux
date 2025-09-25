use std::{
    io::{self, Write},
    process::{Command, Stdio},

};

use flux_middle::{
    def_id::MaybeExternId,
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
};
use liquid_fixpoint::Identifier;

use crate::fixpoint_encoding::fixpoint::{BinRel, ConstDecl, Constraint, Expr, FunDef, Pred, Var};

pub(crate) struct LeanEncoder<'genv, 'tcx> {
    def_id: MaybeExternId,
    genv: GlobalEnv<'genv, 'tcx>,
    fun_defs: Vec<FunDef>,
    constants: Vec<(ConstDecl, Expr)>,
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
        Self {
            def_id,
            genv,
            fun_defs,
            constants: Self::define_constants(constants, &constraint),
            constraint,
        }
    }

    pub fn constants(&self) -> &[(ConstDecl, Expr)] {
        &self.constants
    }

    pub fn fun_defs(&self) -> &[FunDef] {
        &self.fun_defs
    }

    pub fn constraint(&self) -> &Constraint {
        &self.constraint
    }

    pub fn theorem_name(&self) -> String {
        self.genv
            .tcx()
            .def_path(self.def_id.resolved_id())
            .to_filename_friendly_no_crate()
    }

    pub fn proof_name(&self) -> String {
        format!("{}_proof", self.theorem_name()).to_string()
    }

    pub fn generate_def_file(&self) {
        let path = std::path::Path::new("./lean_proofs");
        if !path.exists() {
            Command::new("lake")
                .arg("new")
                .arg("lean_proofs")
                .arg("lib")
                .spawn()
                .and_then(|mut child| child.wait())
                .map(|_| {
                    if let Ok(mut file) = std::fs::File::create(path.join("LeanProofs/Theorem.lean")) {
                        writeln!(file, "{self}");
                    }
                });
        }
    }

    pub fn generate_proof_file(&self) {
        let path = std::path::Path::new("./lean_proofs/LeanProofs/Proof.lean");
        if !path.exists() {
            if let Ok(mut file) = std::fs::File::create(path) {
                writeln!(file, "import LeanProofs.Theorem");
                writeln!(file, "def {} : {} := sorry", self.proof_name(), self.theorem_name());
            }
        }
    }

    fn check_proof_help(&self) -> std::io::Result<()> {
        let child = Command::new("lake")
            .arg("--dir")
            .arg("./lean_proofs")
            .arg("lean")
            .arg("./lean_proofs/LeanProofs/Proof.lean")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let out = child.wait_with_output()?;
        if !out.stderr.is_empty() || !out.stdout.is_empty(){
            let stderr = std::str::from_utf8(&out.stderr)
                .unwrap_or("Lean exited with a non-zero return code");
            Err(io::Error::other(stderr))
        } else {
            Ok(())
        }
    }

    pub fn check_proof(&self) -> QueryResult<()> {
        self.check_proof_help()
            .map_err(|_| QueryErr::Ignored { def_id: self.def_id.resolved_id() })
    }

    fn define_constants(
        constants: Vec<ConstDecl>,
        constraint: &Constraint,
    ) -> Vec<(ConstDecl, Expr)> {
        constants
            .into_iter()
            .map(|const_decl| {
                let mut equality_assumptions = Vec::new();
                Self::collect_constant_equality_assumptions_from_constraint(
                    &const_decl.name,
                    constraint,
                    &mut equality_assumptions,
                );
                if equality_assumptions.len() != 1 {
                    panic!(
                        "Constant {} must have exactly one equality assumption in the constraint",
                        const_decl.name.display()
                    );
                }
                (const_decl, equality_assumptions[0].clone())
            })
            .collect()
    }

    fn collect_constant_equality_assumptions_from_constraint<'a>(
        constant: &Var,
        constraint: &'a Constraint,
        acc: &mut Vec<&'a Expr>,
    ) {
        match constraint {
            Constraint::ForAll(bind, inner) => {
                Self::collect_constant_equality_assumptions_from_constraint(
                    constant,
                    inner.as_ref(),
                    acc,
                );
            }
            Constraint::Conj(cstrs) => {
                for cstr in cstrs {
                    Self::collect_constant_equality_assumptions_from_constraint(
                        constant, &cstr, acc,
                    );
                }
            }
            Constraint::Pred(pred, _) => {
                Self::collect_constant_equality_assumptions_from_pred(constant, &pred, acc);
            }
        }
    }

    fn collect_constant_equality_assumptions_from_pred<'a>(
        constant: &Var,
        pred: &'a Pred,
        acc: &mut Vec<&'a Expr>,
    ) {
        match pred {
            Pred::Expr(Expr::Atom(BinRel::Eq, args)) => {
                if let Expr::Var(var) = &args[0] {
                    if var == constant {
                        acc.push(&args[1]);
                    }
                }
                if let Expr::Var(var) = &args[1] {
                    if var == constant {
                        acc.push(&args[0]);
                    }
                }
            }
            Pred::And(preds) => {
                for p in preds {
                    Self::collect_constant_equality_assumptions_from_pred(constant, p, acc);
                }
            }
            Pred::Expr(_) => {}
            Pred::KVar(_, _) => {}
        }
    }
}
