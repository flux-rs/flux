use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::Local;
use liquid_rust_ty::{LocalVariable, Ty};

use std::fmt;

#[derive(Clone)]
pub(crate) struct Env {
    types: IndexMap<LocalVariable, Ty>,
    variables: Vec<LocalVariable>,
}

impl Env {
    pub(crate) fn new(local_decls: impl Iterator<Item = Ty>) -> Self {
        let mut variables = Vec::new();
        let mut types = IndexMap::new();

        for ty in local_decls {
            let variable = types.insert(ty);
            variables.push(variable);
        }

        Self { variables, types }
    }

    pub(crate) fn get_ty(&self, variable: impl Into<LocalVariable>) -> &Ty {
        self.types.get(variable.into()).unwrap()
    }

    pub(crate) fn rebind_local(&mut self, local: Local, ty: Ty) {
        let local = LocalVariable::from(local);

        for variable in &mut self.variables {
            if *variable == local {
                let old_ty = std::mem::replace(self.types.get_mut(local).unwrap(), ty);

                let ghost = self.types.insert(old_ty);
                *variable = ghost;

                self.variables.push(local);

                for (_, ty) in &mut self.types {
                    ty.replace_variable(local, ghost);
                }
                break;
            }
        }
    }
}

impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vars = self.variables.iter();

        write!(f, "{{")?;

        if let Some(var) = vars.next() {
            let ty = self.types.get(*var).unwrap();
            write!(f, "{}: {}", var, ty)?;

            for var in vars {
                let ty = self.types.get(*var).unwrap();
                write!(f, ", {}: {}", var, ty)?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}
