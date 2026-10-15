use flux_attrs::extern_spec;

// We only infer the refinement of the elements if `new` says they satisfy `false`
#[extern_spec]
impl<T> Vec<T> {
    #[flux::sig(fn() -> Vec<T{v: false}>)]
    fn new() -> Vec<T>;
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

pub fn test() {
    let mut s: Vec<i32> = vec![];
    s.push(0);
    s.push(1);
    for v in &s {
        assert(*v >= 0);
    }
}
