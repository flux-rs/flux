#[flux::spec(fn(f: fn(usize) -> usize[@n]) -> usize)] //~ ERROR illegal binder
pub fn at_in_output(f: fn(usize) -> usize) -> usize {
    f(0)
}

#[flux::spec(fn(f: fn(usize[#n]) -> usize) -> usize)] //~ ERROR illegal binder
pub fn pound_in_input(f: fn(usize) -> usize) -> usize {
    f(0)
}
