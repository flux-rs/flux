use flux_rs::{assert, attrs::*, macros::qualifier};

defs! {
    fn my_plus(x: int, y: int) -> int { x + y }
}

#[spec(fn (n: usize) -> usize[n])]
pub fn test_with_hand_written_qualifier(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        #[flux::defs{
            invariant qualifier Auto(res: int) { res + i == n }
         }]
        const _: () = ();
        assert(res + i == n);
        i -= 1;
        res += 1;
    }
    res
}

/// Same as above, with the sort of `res` annotated. This should expand to exactly the
/// hand-written form.
#[spec(fn (n: usize) -> usize[n])]
pub fn test(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        qualifier!(res: int ; res + i == n);
        assert(res + i == n);
        i -= 1;
        res += 1;
    }
    res
}

/// Sorts are inferred when the body constrains them; here the `n >= 0` conjunct does it.
#[spec(fn (n: usize) -> usize[n])]
pub fn test_inferred_sorts(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        qualifier!(res + i == n && n >= 0);
        assert(res + i == n);
        i -= 1;
        res += 1;
    }
    res
}

/// Two `qualifier!`s in the same function, plus one more in a different function, to check
/// the generated qualifier names don't collide.
#[spec(fn (n: usize) -> usize[n])]
pub fn test_multiple_qualifiers(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        qualifier!(res: int, i: int, n: int ; res + i == n);
        qualifier!(res >= 0 && i >= 0);
        assert(res + i == n);
        i -= 1;
        res += 1;
    }
    res
}

/// The body of `qualifier!` is never re-emitted as Rust, so it can use refinement-only
/// syntax: a call to a refinement function, and `=>`, which is not a Rust operator.
#[spec(fn (n: usize) -> usize[n])]
pub fn test_refinement_syntax(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        qualifier!(my_plus(res, i) == n);
        qualifier!(i >= 0 => res + i == n);
        assert(res + i == n);
        i -= 1;
        res += 1;
    }
    res
}
