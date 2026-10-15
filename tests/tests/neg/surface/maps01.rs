#[path = "../../lib/rmapk.rs"]
mod rmapk;
use rmapk::RMap;

#[flux_attrs::extern_spec]
impl<T> Option<T> {
    #[flux::assume_parametric(T)]
    #[flux::sig(fn(Option<T>) -> T)]
    const fn unwrap(self) -> T;
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut m = RMap::new();
    let k0 = 10;
    let k1 = 20;
    let k2 = 30;

    m.set(k0, 1);
    m.set(k1, 2);

    assert(*m.get(&k1).unwrap() == 2);
    assert(*m.lookup(&k0) == 1);
    assert(*m.lookup(&k1) == 2);
    assert(m.contains(&k0));
    assert(m.contains(&k2)); //~ ERROR refinement type
}
