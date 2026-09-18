use flux_attrs::*;

/// See the note at [`IndexMut`] about also implementing the [`index_mut`] method for any type that implements [`Index`].
#[extern_spec(core::ops)]
trait Index<Idx> {
    #![assoc(fn in_bounds(v: Self, idx: Idx) -> bool { true })]
    #![assoc(fn output_pred(v: Self, idx: Idx, out: Self::Output) -> bool { true })]

    #[sig(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &Self::Output{out: <Self as Index<Idx>>::output_pred(v, index, out)})]
    fn index(&self, index: Idx) -> &Self::Output;
}

/// [NOTE:The [`IndexMut`] trait is a subtrait of [`Index`],
/// hence any (refined) impl of `Index` should now *also*
/// have a matching (refined) impl for `IndexMut` as otherwise
/// the latter will either
/// - fail the impl-subtyping, (e.g. in the case of regular specs), or worse
/// - be silently inconsistent (e.g. in the case of extern-specs).
#[extern_spec(core::ops)]
trait IndexMut<Idx>: Index<Idx> {
    #[sig(fn(self: &mut Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &mut Self::Output{out: <Self as Index<Idx>>::output_pred(v, index, out)})]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
