use flux_attrs::*;

#[extern_spec(core::ops)]
trait Index<Idx> {
    #![assoc(fn in_bounds(v: Self, idx: Idx) -> bool { true })]
    #![assoc(fn output_pred(v: Self, idx: Idx, out: Self::Output) -> bool { true })]

    #[sig(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &Self::Output{out: <Self as Index<Idx>>::output_pred(v, index, out)})]
    fn index(&self, index: Idx) -> &Self::Output;
}

/// Without a trait-level spec, `index_mut`'s signature is the unrefined lifted one, so any impl
/// carrying an `in_bounds` precondition fails the impl-vs-trait subtyping check. `IndexMut: Index`,
/// so the two associated refinements are inherited rather than redeclared — the same way
/// `flux-core`'s own `[T]` and `[T; N]` `IndexMut` impls are written.
#[extern_spec(core::ops)]
trait IndexMut<Idx>: Index<Idx> {
    #[sig(fn(self: &mut Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &mut Self::Output{out: <Self as Index<Idx>>::output_pred(v, index, out)})]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
