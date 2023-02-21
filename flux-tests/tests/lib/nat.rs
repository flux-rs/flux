#[flux::alias(type Nat = i32{v: 0 <= v})]
pub type Nat = i32;

#[flux::alias(type Lb(n: int) = i32{v: n <= v})]
pub type Lb = i32;
