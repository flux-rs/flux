#[flux::spec(fn(base: usize, off: usize{base <= off}) -> usize[off - base])]
fn foo(base: usize, off: usize) -> usize {
    off - base
}

#[flux::spec(fn(tagged: usize, off: usize, f: fn(usize) -> usize{v: v <= off}) -> usize)]
pub fn bar(tagged: usize, off: usize, f: fn(usize) -> usize) -> usize {
    let buf = f(tagged);
    foo(buf, off)
}

#[flux::spec(fn(x: usize) -> usize{v: v <= 10})]
fn clamp10(x: usize) -> usize {
    if x <= 10 { x } else { 10 }
}

pub fn caller_ok(tagged: usize) -> usize {
    bar(tagged, 10, clamp10) + bar(tagged, 20, clamp10)
}

// constant refinement, input refinement, unit return
#[flux::spec(fn(f: fn(usize{v: v > 0}) -> usize{v: v > 0}) -> usize{v: v > 0})]
pub fn pos(f: fn(usize) -> usize) -> usize {
    f(5)
}

#[flux::spec(fn(f: fn(usize{v: v < 100})))]
pub fn unit_ret(f: fn(usize)) {
    f(3)
}
