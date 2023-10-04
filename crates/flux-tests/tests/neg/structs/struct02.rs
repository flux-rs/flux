// Strong update trough nested structs

#[flux::refined_by(a: int)]
struct S1 {
    f1: i32,
    #[flux::field(S2[a])]
    f2: S2,
}

#[flux::refined_by(a: int)]
struct S2 {
    #[flux::field(i32[a])]
    f1: i32,
}

#[flux::sig(fn(x: &strg S1[@n]) ensures x: S1[n] )]
fn test(x: &mut S1) {
    //~^ ERROR refinement type
    let r = &mut x.f2.f1;
    *r += 1;
}
