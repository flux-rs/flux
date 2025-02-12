use flux_attrs::*;

#[extern_spec(core::ops)]
#[assoc(fn in_bounds(v: Self, idx: Idx) -> bool { true })]
trait Index<Idx> {
    #[sig(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &Self::Output)]
    fn index(&self, index: Idx) -> &Self::Output;
}
