// Test we convert existential in type aliases into type constructors

#[flux::alias(type Nat = i32{v: 0 <= v})]
type Nat = i32;

#[flux::alias(type Lb(n: int) = i32{v: n <= v})]
type Lb = i32;

#[flux::sig(fn(x: Nat) -> i32{v: v >= 0})]
pub fn test0(x: Nat) -> i32 {
    x - 1 //~ ERROR refinement type
}

#[flux::sig(fn(x: Lb(0)) -> Lb(10))]
pub fn test2(x: Lb) -> Lb {
    x + 1 //~ ERROR refinement type
}
