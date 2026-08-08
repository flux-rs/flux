// Test that a qualifier parameter marked as a wildcard with `#` is instantiated with the literal
// constants appearing in the constraint. Proving the loop below exits with `i == 10` needs the
// invariant `i <= 10`, which is specific to the literal `10`, so `LeLit` can only work if `a` is
// instantiated with it.

#![flux::defs {
    qualifier LeLit(x: int, a #: int) { x <= a }
}]

#[flux::sig(fn() -> usize[10])]
pub fn count_to_ten() -> usize {
    let mut i = 0;
    while i < 10 {
        i += 1;
    }
    i
}
