#[flux::refined_by(n: int)]
struct S<T> {
    f: T,
    #[flux::field(i32[n])]
    _n: i32,
}

#[flux::alias(type A[n: int] = S<i32[n]>[n])]
type A = S<i32>;

fn test00<T>(x: &mut T) {}

fn test01(x: &mut A) {
    // This produces the subtyping
    // &mut ∃a. S<i32[a]>[a]
    //   <: &mut ∃b. { S<∃c. { i32[c] | $k1 }>[b] | $k0 }
    // We are testing that $k1 should be able to mention both c and b.
    test00(x);
}
