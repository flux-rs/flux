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

static VTABLE: Vtable = Vtable { clone: clone_impl };

// VERIFIES. The call goes through the fn-pointer field, whose (dependent) spec says the
// result is `Handle[h]`. The initializer of `VTABLE` is checked against that spec.
#[flux::spec(fn(&Handle[@h]) -> Handle[h])]
pub fn clone_via_vtable(h: &Handle) -> Handle {
    (VTABLE.clone)(h)
}

// VERIFIES. Same function, called directly: the spec is available.
#[flux::spec(fn(&Handle[@h]) -> Handle[h])]
pub fn clone_direct(h: &Handle) -> Handle {
    clone_impl(h)
}
