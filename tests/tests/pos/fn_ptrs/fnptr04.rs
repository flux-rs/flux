#[flux::spec(fn(base: usize, off: usize{base <= off}) -> usize[off - base])]
fn foo(base: usize, off: usize) -> usize {
    off - base
}

#[flux::spec(fn(tagged: usize, off: usize, f: fn(usize) -> usize{v: v <= off}) -> usize)]
pub fn bar_ok(tagged: usize, off: usize, f: fn(usize) -> usize) -> usize {
    let buf = f(tagged);
    foo(buf, off)
}

#[flux::spec(fn(tagged: usize, off: usize, f: F) -> usize where F: FnOnce(usize) -> usize{v: v <= off})]
pub fn baz_ok<F: FnOnce(usize) -> usize>(tagged: usize, off: usize, f: F) -> usize {
    let buf = f(tagged);
    foo(buf, off)
}
