use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::{Local, Operand};
use liquid_rust_ty::{LocalVariable, Predicate, Ty, Variable};

use std::fmt;

#[derive(Clone)]
pub(crate) struct Env {
    variables: IndexMap<Local, LocalVariable>,
    types: IndexMap<LocalVariable, Ty>,
    substitutions: Vec<Substitution>,
}

impl Env {
    pub(crate) fn new(local_decls: impl Iterator<Item = Ty>) -> Self {
        let mut variables = IndexMap::new();
        let mut types = IndexMap::new();

        for ty in local_decls {
            let variable = types.insert(ty);
            variables.insert(variable);
        }

        Self {
            variables,
            types,
            substitutions: vec![],
        }
    }

    pub(crate) fn get_ty(&self, variable: LocalVariable) -> &Ty {
        self.substitutions
            .iter()
            .rev()
            .find_map(|subst| {
                if subst.target == variable {
                    Some(&subst.ty)
                } else {
                    None
                }
            })
            .unwrap_or_else(|| self.types.get(variable).unwrap())
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
    pub(crate) fn substitute(&mut self, target: LocalVariable, ty: Ty) {
        self.substitutions.push(Substitution::new(target, ty));
    }
}

impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut types = self.types.iter();

        write!(f, "{{")?;

        if let Some((var, ty)) = types.next() {
            write!(f, "{}: {}", var, ty)?;

            for (var, ty) in types {
                write!(f, ", {}: {}", var, ty)?;
            }
        }

        write!(f, "}}")?;

        for subst in &self.substitutions {
            write!(f, "{}", subst)?;
        }

        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct Substitution {
    target: LocalVariable,
    ty: Ty,
}

impl Substitution {
    pub(crate) fn new(target: LocalVariable, ty: Ty) -> Self {
        Self { target, ty }
    }
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{} -> {}]", self.target, self.ty)
    }
}
