#[flux::refined_by(hrn p: int -> bool)]
struct S {
    #[flux::field(i32{v: p(v)})]
    x: i32,
}

fn test00() {
    // Check we properly infer horn generic when constructing struct
    check_ge0(S { x: 0 });
}

fn test01() {
    let mut s = S { x: 0 };
    s.x += 1;
    // Check we properly infer horn generic when folding
    check_ge0(s);
}

#[flux::spec(
fn check_ge0(x: S[|x| x >= 0]))]
fn check_ge0(x: S) {}
