use flux_attrs::*;

#[extern_spec]
#[flux::assoc(fn with_size(self: Self, n:int) -> bool { true })] // default: don't know!
trait FromIterator<A> {}
