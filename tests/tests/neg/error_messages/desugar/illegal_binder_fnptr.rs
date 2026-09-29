#[flux::spec(fn(f: fn(usize[@n]) -> usize[n]) -> usize)] //~ ERROR illegal binder
pub fn implicit(f: fn(usize) -> usize) -> usize {
    f(0)
}
