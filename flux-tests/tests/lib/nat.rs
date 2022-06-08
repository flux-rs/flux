#[flux::alias(type Nat() = i32{v: 0 <= v})]
pub type Nat = i32;

#[flux::alias(type Lb(n) = i32{v: n <= v})]
pub type Lb = i32;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test(x: i32) -> i32 {
    x + 1
}
