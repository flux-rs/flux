use liquid_rust_common::index::IndexGen;
use liquid_rust_mir::ty::{Ghost, Ty, Variable};

use std::{fmt, rc::Rc};

#[derive(Clone)]
pub(crate) struct LocalEnv {
    types: Vec<(Variable, Ty)>,
    generator: Rc<IndexGen<Ghost>>,
}

impl LocalEnv {
    pub(crate) fn empty(generator: Rc<IndexGen<Ghost>>) -> Self {
        Self {
            types: Vec::new(),
            generator,
        }
    }

    pub(crate) fn spawn_empty(&self) -> Self {
        Self::empty(Rc::clone(&self.generator))
    }

    pub(crate) fn bind(&mut self, variable: Variable, ty: Ty) {
        self.types.push((variable, ty));
    }

    pub(crate) fn rebind(&mut self, old_variable: Variable, mut ty: Ty) {
        let new_variable = Variable::Ghost(self.generator.generate());

        ty.replace_variable(old_variable, new_variable);

        let mut has_variable = false;

        for (variable, ty) in self.types.iter_mut() {
            if *variable == old_variable {
                *variable = new_variable;
                has_variable = true;
            }
            ty.replace_variable(old_variable, new_variable);
        }

        assert!(
            has_variable,
            "Rebound variable is not in env: {}",
            old_variable
        );

        self.bind(old_variable, ty);
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &(Variable, Ty)> {
        self.types.iter()
    }

    pub(crate) fn first(&self) -> Option<Variable> {
        Some(self.types.first()?.0)
    }

    pub(crate) fn first_ty(&self) -> Option<&Ty> {
        Some(&self.types.first()?.1)
    }

    pub(crate) fn remove_first(&mut self) -> (Variable, Ty) {
        self.types.remove(0)
    }

    pub(crate) fn get_ty(&self, target: Variable) -> Option<&Ty> {
        self.types
            .iter()
            .find_map(|(variable, ty)| (*variable == target).then(|| ty))
    }
}

impl fmt::Display for LocalEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut vars = self.types.iter();

        write!(f, "{{")?;

        if let Some((var, ty)) = vars.next() {
            write!(f, "{}: {}", var, ty)?;

            for (var, ty) in vars {
                write!(f, ", {}: {}", var, ty)?;
            }
        }

        write!(f, "}}")
    }
}
