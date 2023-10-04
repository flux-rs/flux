// Test: variants from enums without a refined_by should be refinable

enum S {
    #[flux::variant((i32{v: v >= 0}) -> S)]
    A(i32),
}

#[flux::sig(fn(x: S) -> i32{v: v > 0})]
fn test00(x: S) -> i32 {
    let S::A(x) = x;
    x //~ ERROR refinement type
}
