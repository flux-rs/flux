#[flux::alias(type Nat = i32{v: v >= 0})]
type Nat = i32;

// This should not crash
#[flux::sig(fn(&mut Nat{v: true}))]
fn test(x: &mut Nat) {}
