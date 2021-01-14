use liquid_rust_common::index::Index;
use liquid_rust_mir::Local;
use liquid_rust_ty::{LocalVariable, Ty};

use std::fmt;

#[derive(Clone)]
pub(crate) struct Env {
    types: Vec<(LocalVariable, Ty)>,
    len_locals: usize,
}

impl Env {
    pub(crate) fn empty(len_locals: usize) -> Self {
        Self {
            types: Vec::new(),
            len_locals,
        }
    }

    pub(crate) fn new(local_decls: impl Iterator<Item = Ty>) -> Self {
        let mut types = Vec::new();

        for ty in local_decls {
            let variable = LocalVariable::new(types.len());
            types.push((variable, ty));
        }

        Self {
            len_locals: types.len(),
            types,
        }
    }

    pub(crate) fn len_locals(&self) -> usize {
        self.len_locals
    }

    pub(crate) fn len(&self) -> usize {
        self.types.len()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &(LocalVariable, Ty)> {
        self.types.iter()
    }

    pub(crate) fn get_ty(&self, target: impl Into<LocalVariable>) -> &Ty {
        let target = target.into();
        self.types
            .iter()
            .find_map(
                |(variable, ty)| {
                    if *variable == target {
                        Some(ty)
                    } else {
                        None
                    }
                },
            )
            .unwrap_or_else(|| panic!("couldn't find {} in {}.", target, self))
    }

    pub(crate) fn bind(&mut self, var: LocalVariable, ty: Ty) {
        self.types.push((var, ty));
    }

    pub(crate) fn rebind_local(&mut self, local: Local, ty: Ty) {
        let local = LocalVariable::from(local);
        let ghost = LocalVariable::new(self.types.len());

        for (variable, old_ty) in &mut self.types {
            if *variable == local {
                let old_ty = std::mem::replace(old_ty, ty);

                self.types.push((ghost, old_ty));

                for (_, ty) in &mut self.types {
                    ty.map_variable(|var| if var == local { ghost } else { var });
                }
                break;
            }
        }
    }
}

impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vars = self.types.iter();

        write!(f, "{{")?;

        if let Some((var, ty)) = vars.next() {
            write!(f, "{}: {}", var, ty)?;

            for (var, ty) in vars {
                write!(f, ", {}: {}", var, ty)?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}
