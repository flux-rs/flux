pub struct S<const N: usize = 1>;

pub fn use_default(_: S) {}

pub struct Dep<const N: usize, const M: usize = N>;

pub fn use_dependent_default(_: Dep<3>) {}

pub fn use_generic_default<const N: usize>(_: Dep<N>) {}

#[flux_attrs::sig(fn(Dep<_>))]
pub fn use_inferred_default(_: Dep<3>) {}

pub struct Chain<const N: usize, const M: usize = N, const K: usize = M>;

pub fn use_chained_defaults<const N: usize>(_: Chain<N>) {}
