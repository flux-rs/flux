#[flux::spec(fn(x: usize) -> usize{v: v <= 10})]
fn clamp10(x: usize) -> usize {
    if x <= 10 { x } else { 10 }
}

#[flux::spec(fn(x: usize{x > 0}) -> usize)]
fn needs_pos(x: usize) -> usize {
    x
}

fn apply(f: fn(usize) -> usize) -> usize {
    f(0)
}

// `needs_pos` cannot be used where any `usize` may be passed
pub fn caller() -> usize {
    apply(needs_pos) //~ ERROR refinement type
}

#[flux::spec(fn(usize) -> usize{v: v <= 5})]
pub fn call_local_bad(x: usize) -> usize {
    let f: fn(usize) -> usize = clamp10;
    f(x) //~ ERROR refinement type
}

#[flux::spec(fn(x: i32[@n]) -> i32[n + 1])]
fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::spec(fn(x: i32) -> i32[x + 3])]
pub fn twice_bad(x: i32) -> i32 {
    let f: fn(i32) -> i32 = inc;
    f(f(x)) //~ ERROR refinement type
}

// The joined fn pointer is called with `0`, which `needs_pos` does not accept
pub fn join_input_bad(b: bool) -> usize {
    let f: fn(usize) -> usize = if b { needs_pos } else { clamp10 }; //~ ERROR refinement type
    f(0)
}

#[flux::spec(fn(x: usize) -> usize{v: v <= 5})]
fn clamp5(x: usize) -> usize {
    if x <= 5 { x } else { 5 }
}

#[flux::spec(fn(bool, usize) -> usize{v: v <= 5})]
pub fn join_output_bad(b: bool, x: usize) -> usize {
    let f: fn(usize) -> usize = if b { clamp10 } else { clamp5 };
    f(x) //~ ERROR refinement type
}

#[flux::spec(fn(x: usize) -> usize{v: v < x} requires x > 0)]
fn dec(x: usize) -> usize {
    x - 1
}

pub fn join_requires_bad(b: bool) -> usize {
    let f: fn(usize) -> usize = if b { dec } else { clamp10 }; //~ ERROR refinement type
    f(0)
}
