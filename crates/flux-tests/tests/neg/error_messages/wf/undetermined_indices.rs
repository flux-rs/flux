// Unused parameter
#[flux::refined_by(n: int)] //~ ERROR parameter `n` cannot be determined
struct S1 {
    x: Vec<i32>,
}

// Used but not determined
#[flux::refined_by(n: int)] //~ ERROR parameter `n` cannot be determined
struct S2 {
    #[flux::field(Vec<i32[n]>)]
    x: Vec<i32>,
}

#[flux::alias(type A[n: int] = i32{v: v > n})] //~ ERROR parameter `n` cannot be determined
type A = i32;

// Undetermined parameter in general existential
#[flux::sig(fn({a:int. {i32 | a > 0}}))] //~ ERROR parameter `a` cannot be determined
fn test01(x: i32) {}

// Undetermined parameter in multi param existential
#[flux::sig(fn({a:int,b:int. i32[a]}))] //~ ERROR parameter `b` cannot be determined
fn test02(x: i32) {}
