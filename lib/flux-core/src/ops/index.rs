use flux_attrs::*;

#[extern_spec(core::ops)]
trait Index<Idx> {
    #![assoc(fn in_bounds(v: Self, idx: Idx) -> bool { true })]
<<<<<<< HEAD
    #![assoc(fn is_valid_at(v: Self, idx: Idx, out: Self::Output) -> bool { true })]

    #[sig(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &Self::Output{out: <Self as Index<Idx>>::is_valid_at(v, index, out)})]
=======
    #![assoc(fn output_pred(v: Self, idx: Idx, out: Self::Output) -> bool { true })]

    #[sig(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) -> &Self::Output{out: <Self as Index<Idx>>::output_pred(v, index, out)})]
>>>>>>> b6b7cbc3a506de4da0326d2eddf8c6818d36003d
    fn index(&self, index: Idx) -> &Self::Output;
}
