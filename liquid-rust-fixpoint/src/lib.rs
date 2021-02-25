mod constant;
mod constraint;
mod embed;
mod emit;
mod pred;
mod sort;
mod variable;

use embed::Embed;
use emit::{Emit, Emitter};

pub struct Fixpoint {}

impl Fixpoint {
    fn embed<E: Embed>(&self, e: &E) -> E::Output {
        e.embed(self)
    }
}
