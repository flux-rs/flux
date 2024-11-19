// Test we convert existential in type aliases into type constructors

#[flux::alias(type Nat = i32{n: 0 <= n})]
type Nat = i32;

#[flux::alias(type Lb(n: int) = i32{v: n <= v})]
type Lb = i32;

#[flux::sig(fn(x: Nat) -> Nat)]
pub fn test1(x: Nat) -> Nat {
    x + 1
}

#[flux::sig(fn(x: Lb(10)) -> Lb(10))]
pub fn test2(x: Lb) -> Lb {
    x + 1
}
