use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::{Local, Operand};
use liquid_rust_ty::{LocalVariable, Predicate, Ty, Variable};

use std::fmt;

#[derive(Clone)]
pub(crate) struct Env {
    variables: IndexMap<Local, LocalVariable>,
    types: IndexMap<LocalVariable, Ty>,
}

impl Env {
    pub(crate) fn new(local_decls: impl Iterator<Item = Ty>) -> Self {
        let mut variables = IndexMap::new();
        let mut types = IndexMap::new();

        for ty in local_decls {
            let variable = types.insert(ty);
            variables.insert(variable);
        }

        Self { variables, types }
    }

    pub(crate) fn get_ty(&self, variable: LocalVariable) -> &Ty {
        self.types.get(variable).unwrap()
    }

    pub(crate) fn resolve_local(&self, local: Local) -> LocalVariable {
        *self.variables.get(local).unwrap()
    }

    pub(crate) fn resolve_operand(&self, operand: &Operand) -> Predicate {
        match operand {
            Operand::Local(local) => Predicate::Var(Variable::Local(self.resolve_local(*local))),
            Operand::Literal(literal) => Predicate::Lit(*literal),
        }
    }

    pub(crate) fn rebind_local(&mut self, local: Local, ty: Ty) {
        let variable = self.types.insert(ty);
        *self.variables.get_mut(local).unwrap() = variable;
    }
}

impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bound_vars = vec![];
        let mut vars = self.variables.iter();

        write!(f, "{{")?;

        if let Some((local, var)) = vars.next() {
            bound_vars.push(*var);
            let ty = self.types.get(*var).unwrap();
            write!(f, "{} -> {}: {}", var, local, ty)?;

            for (local, var) in vars {
                bound_vars.push(*var);
                let ty = self.types.get(*var).unwrap();
                write!(f, "{} -> {}: {}", var, local, ty)?;
            }
        }

        let types = self
            .types
            .iter()
            .filter(|(var, _)| !bound_vars.contains(var));

        for (var, ty) in types {
            write!(f, ", {}: {}", var, ty)?;
        }

        write!(f, "}}")?;

        Ok(())
    }
}
