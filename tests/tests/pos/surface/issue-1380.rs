#[flux::opaque]
#[flux::refined_by(len: int, hdl get: int -> bool)]
struct Slot([bool]);

impl Slot {
    #[flux::trusted]
    #[flux::sig(
        fn(self: &strg Slot[@n, @f], i: usize{i < n})
        ensures self: Slot[n, |j| j == i || f(j)]
    )]
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
