#[flux::alias(type Nat[v: int] = {i32[v] | 0 <= v})]
pub type Nat = i32;

#[flux::alias(type Lb(n: int)[v: int] = {i32[v] | n <= v})]
pub type Lb = i32;
