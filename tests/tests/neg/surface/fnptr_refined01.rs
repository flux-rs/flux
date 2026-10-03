#[flux::refined_by(n: int)]
pub struct Handle {
    #[flux::field(usize[n])]
    n: usize,
}

#[flux::refined_by()]
pub struct Vtable {
    #[flux::field(fn(&Handle[@h]) -> Handle[h])]
    clone: fn(&Handle) -> Handle,
}

fn clone_wrong(h: &Handle) -> Handle {
    Handle { n: h.n + 1 }
}

pub fn make_bad_vtable() -> Vtable {
    Vtable { clone: clone_wrong } //~ ERROR refinement type
}

#[flux::spec(fn(x: usize, f: fn(usize[@n]) -> usize{v: v > n}) -> usize{v: v > x + 1})]
pub fn call_dep2_bad(x: usize, f: fn(usize) -> usize) -> usize {
    f(x) //~ ERROR refinement type
}
