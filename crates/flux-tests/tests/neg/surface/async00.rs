#[flux::alias(type Nat = i32{v: 0 <= v})]
pub type Nat = i32;

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub async fn bar(y: Nat) -> Nat {
    let z = if y > 10 { 1 } else { 0 };
    assert(z > 0); //~ ERROR refinement type
    assert(z >= 0);
    assert(y >= 0);
    z + 999
}
