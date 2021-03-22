mod constant;
mod constraint;
mod embed;
mod emit;
mod pred;
mod sort;

use embed::Embed;
use emit::Emit;

use liquid_rust_lrir::ty::Var;

pub use constraint::Constraint;

#[derive(Default)]
pub struct Fixpoint {
    scope: Vec<Var>,
}

impl Fixpoint {
    pub fn push_var(&mut self, var: Var) -> usize {
        let index = self.scope.len();
        self.scope.push(var);
        index
    }

    pub fn pop_var(&mut self) -> Var {
        self.scope.pop().unwrap()
    }

    fn get_index(&self, target: &Var) -> usize {
        for (index, var) in self.scope.iter().enumerate() {
            if var == target {
                return index;
            }
        }
        panic!()
    }

    pub fn embed<E: Embed>(&self, e: &E) -> E::Output {
        e.embed(self)
    }

    pub fn emit<E: Emit, W: std::fmt::Write>(&self, e: &E, w: &mut W) -> std::fmt::Result {
        e.emit(w, &0)
    }
}
