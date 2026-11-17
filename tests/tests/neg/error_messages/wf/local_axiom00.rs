use flux_attrs::*;

defs! {
    fn f(x: int) -> int;

    local axiom FPos(x: int) { f(x) > 0 }

    local qualifier Bound(x: int, y: int) { x <= y }
}

#[axioms(FNeg)] //~ ERROR unknown axiom
pub fn test00() {}

#[axioms(Bound)] //~ ERROR unknown axiom
pub fn test01() {}

#[qualifiers(FPos)] //~ ERROR unknown qualifier
pub fn test02() {}
