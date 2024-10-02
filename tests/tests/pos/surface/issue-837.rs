use flux_rs::*;

#[generics(Self as base)]
trait Trait {}

fn test00(x: &dyn Trait) {}
