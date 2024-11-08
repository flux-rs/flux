#[flux::alias(type Nat[n: int] = {i32[n] | 0 <= n})]
type Nat = i32;

#[flux::alias(type Lb(n: int)[v: int] = {i32[v] | n <= v})]
type Lb = i32;

#[flux::sig(fn(x: Nat) -> Nat)]
pub fn test1(x: Nat) -> Nat {
    x + 1
}

#[flux::sig(fn(x: Lb(10)) -> Lb(10))]
pub fn test2(x: Lb) -> Lb {
    x + 1
}
