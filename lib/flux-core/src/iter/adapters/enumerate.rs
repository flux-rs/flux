use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(idx: int, inner: I)]
struct Enumerate<I>;
