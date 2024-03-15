#![flux::cfg(scrape_quals = true)]

#[flux::sig(fn<T as base, refine p: T -> bool>(vec: Vec<T{v: p(v)}>, init: T{ p(init) }) -> T{v: p(v)})]
fn maximum<T: Ord>(vec: Vec<T>, init: T) -> T {
    let mut max = init;
    for v in vec {
        if let std::cmp::Ordering::Greater = max.cmp(&v) {
            max = v;
        }
    }
    max
}
