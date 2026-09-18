use flux_attrs::*;

fn assert(_: bool) {}

#[flux::sig(fn() -> {a, b. (usize[a], usize[b]) | a < b})]
fn tuple() -> (usize, usize) {
    (10, 20)
}

#[flux::sig(fn() -> [{a, b. (usize[a], usize[b]) | a < b}; 2])]
fn tuples() -> [(usize, usize); 2] {
    let x0 = tuple();
    let x1 = tuple();
    [x0, x1]
}

fn test() {
    let xs = tuples();
    let (a, b) = xs[0];
    assert(a < b);
}
