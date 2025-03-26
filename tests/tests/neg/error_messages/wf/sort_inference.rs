#[flux::refined_by(hrn p: int -> bool)]
struct S;

#[flux::sig(fn(S[|a: bool| a]))] //~ ERROR mismatched sorts
fn test01(x: S) {}
