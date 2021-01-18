use liquid_rust_common::index::{IndexMap};
use liquid_rust_ty::{LocalVariable, Ty};

use std::fmt;

#[derive(Clone)]
pub(crate) struct Env {
    types: IndexMap<LocalVariable, Ty>,
    binds: Vec<(LocalVariable, Ty)>,
}

impl Env {
    pub(crate) fn empty() -> Self {
        Self {
            types: IndexMap::new(),
            binds: Vec::new(),
        }
    }

    pub(crate) fn new(local_decls: impl Iterator<Item = Ty>) -> Self {
        let mut types = IndexMap::new();

        for ty in local_decls {
            types.insert(ty);
        }

        Self {
            types,
            binds: Vec::new(),
        }
    }

    pub(crate) fn len_locals(&self) -> usize {
        self.types.len()
    }

    pub(crate) fn len_binds(&self) -> usize {
        self.binds.len()
    }

    pub(crate) fn len(&self) -> usize {
        self.types.len() + self.binds.len()
    }

    pub(crate) fn types(&self) -> impl Iterator<Item = (LocalVariable, &Ty)> {
        self.types.iter()
    }

    pub(crate) fn binds(&self) -> impl Iterator<Item = &(LocalVariable, Ty)> {
        self.binds.iter()
    }

    pub(crate) fn get_ty(&self, target: impl Into<LocalVariable>) -> &Ty {
        let target = target.into();
        if let Some((_, ty)) = self
            .binds
            .iter()
            .rev()
            .find(|(variable, _)| *variable == target)
        {
            ty
        } else {
            self.types
                .get(target)
                .unwrap_or_else(|| panic!("couldn't find {} in {}.", target, self))
        }
    }

    pub(crate) fn bind(&mut self, local: impl Into<LocalVariable>, ty: Ty) {
        assert_eq!(local.into(), self.types.insert(ty))
    }

    pub(crate) fn rebind_local(&mut self, local: impl Into<LocalVariable>, ty: Ty) {
        self.binds.push((local.into(), ty));
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
