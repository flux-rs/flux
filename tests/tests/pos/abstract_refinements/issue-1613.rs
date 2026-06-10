// https://github.com/flux-rs/flux/issues/1613
// Updating an abstract refinement on a composite-sort field behind a `&mut`, where the field
// invariant only mentions a *preserved* projection (`slot.len`). The setter changes the `hdl`
// refinement but keeps `len`, so re-folding `Container` (which only needs `slot.len > 0`) holds.
#[flux::opaque]
#[flux::refined_by(len: int, hdl get: int -> bool)]
struct Slot([bool]);

impl Slot {
    #[flux::trusted]
    #[flux::sig(fn(self: &strg Slot[@n, @f], i: usize{i < n})
                ensures self: Slot[n, |j| j == i || f(j)])]
    fn set(&mut self, i: usize) {
        self.0[i] = true;
    }
}

#[flux::refined_by(slot: Slot)]
struct Container<'a> {
    #[flux::field({&mut Slot[slot] | slot.len > 0})]
    slot: &'a mut Slot,
}

impl<'a> Container<'a> {
    #[flux::sig(fn(self: &strg Container[@s]) ensures self: Container)]
    fn update(&mut self) {
        self.slot.set(0);
    }
}

// Same shape with plain integer-sort components instead of a function sort. The fix is keyed to
// the field-projection borrow, not to the sort, so this must also verify. (Guards against a
// narrower fix that only special-cases function-sort fields.)
#[flux::opaque]
#[flux::refined_by(len: int, val: int)]
struct IntSlot([bool]);

impl IntSlot {
    #[flux::trusted]
    #[flux::sig(fn(self: &strg IntSlot[@n, @v], i: usize{i < n})
                ensures self: IntSlot[n, v + 1])]
    fn set(&mut self, i: usize) {
        let _ = i;
    }
}

#[flux::refined_by(slot: IntSlot)]
struct IntContainer<'a> {
    #[flux::field({&mut IntSlot[slot] | slot.len > 0})]
    slot: &'a mut IntSlot,
}

impl<'a> IntContainer<'a> {
    #[flux::sig(fn(self: &strg IntContainer[@s]) ensures self: IntContainer)]
    fn update(&mut self) {
        self.slot.set(0);
    }
}
