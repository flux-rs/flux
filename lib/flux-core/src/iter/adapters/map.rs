use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(inner: I)]
struct Map<I, F>;
