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

#[flux::spec(fn(&Handle[@h]) -> Handle[h])]
fn clone_impl(h: &Handle) -> Handle {
    Handle { n: h.n }
}

#[flux::spec(fn(h: &Handle[@k], f: fn(&Handle[@h]) -> Handle[h]) -> Handle[k])]
pub fn call_dep(h: &Handle, f: fn(&Handle) -> Handle) -> Handle {
    f(h)
}

#[flux::spec(fn(x: usize, f: fn(usize[@n]) -> usize{v: v > n}) -> usize{v: v > x})]
pub fn call_dep2(x: usize, f: fn(usize) -> usize) -> usize {
    f(x)
}

#[flux::spec(fn(vt: &Vtable, h: &Handle[@k]) -> Handle[k])]
pub fn via_field(vt: &Vtable, h: &Handle) -> Handle {
    (vt.clone)(h)
}

pub fn make_vtable() -> Vtable {
    Vtable { clone: clone_impl }
}

pub fn use_dep(h: &Handle) -> Handle {
    call_dep(h, clone_impl)
}
