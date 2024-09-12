#[flux::assoc(fn f(x: int) -> int { x > 1 })]   //~ ERROR mismatched sorts
pub trait MyTrait {}

