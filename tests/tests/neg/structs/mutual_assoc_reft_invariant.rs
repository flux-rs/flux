#[flux::assoc(fn lower_bound() -> int)]
trait HasLowerBound {}

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <B as HasLowerBound>::lower_bound())]
struct A {
    #[flux::field(usize[n])]
    value: usize,
}

#[flux::refined_by(n: int)]
#[flux::invariant(n >= <A as HasLowerBound>::lower_bound())]
struct B {
    #[flux::field(usize[n])]
    value: usize,
}

#[flux::assoc(fn lower_bound() -> int { 1 })]
impl HasLowerBound for A {}

#[flux::assoc(fn lower_bound() -> int { 1 })]
impl HasLowerBound for B {}

fn make_a() -> A {
    A { value: 0 } //~ ERROR refinement type
}

fn make_b() -> B {
    B { value: 0 } //~ ERROR refinement type
}
