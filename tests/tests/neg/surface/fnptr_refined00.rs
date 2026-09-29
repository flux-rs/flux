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

pub fn caller_bad(tagged: usize) -> usize {
    bar(tagged, 5, clamp10) //~ ERROR refinement type
}

#[flux::spec(fn(off: usize, f: fn(usize) -> usize{v: v <= off + 1}) -> usize)]
pub fn body_bad(off: usize, f: fn(usize) -> usize) -> usize {
    foo(f(0), off) //~ ERROR refinement type
}

#[flux::spec(fn(f: fn(usize{v: v > 0}) -> usize) -> usize)]
pub fn arg_bad(f: fn(usize) -> usize) -> usize {
    f(0) //~ ERROR refinement type
}

#[flux::spec(fn(x: usize{x > 0}) -> usize)]
fn needs_pos(x: usize) -> usize {
    x
}

#[flux::spec(fn(f: fn(usize) -> usize) -> usize)]
fn apply(f: fn(usize) -> usize) -> usize {
    f(0)
}

pub fn caller_contra() -> usize {
    apply(needs_pos) //~ ERROR refinement type
}
