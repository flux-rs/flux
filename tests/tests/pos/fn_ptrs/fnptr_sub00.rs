#[flux::spec(fn(x: usize) -> usize{v: v <= 10})]
fn clamp10(x: usize) -> usize {
    if x <= 10 { x } else { 10 }
}

#[flux::spec(fn(x: usize) -> usize{v: v <= 5})]
fn clamp5(x: usize) -> usize {
    if x <= 5 { x } else { 5 }
}

// A call through a fn pointer uses the (precise) signature of the fn
#[flux::spec(fn(usize) -> usize{v: v <= 10})]
pub fn call_local(x: usize) -> usize {
    let f: fn(usize) -> usize = clamp10;
    f(x)
}

// The early refinement params of the fn become late-bound params of the fn pointer
#[flux::spec(fn(x: i32[@n]) -> i32[n + 1])]
fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::spec(fn(x: i32) -> i32[x + 2])]
pub fn twice(x: i32) -> i32 {
    let f: fn(i32) -> i32 = inc;
    f(f(x))
}

// Passing a fn pointer where an (unrefined) fn pointer is expected
fn apply(f: fn(usize) -> usize, x: usize) -> usize {
    f(x)
}

pub fn call_apply(x: usize) -> usize {
    apply(clamp10, x)
}

// Fn pointers from different branches are joined into a signature with kvars
#[flux::spec(fn(bool, usize) -> usize{v: v <= 10})]
pub fn join(b: bool, x: usize) -> usize {
    let f: fn(usize) -> usize = if b { clamp10 } else { clamp5 };
    f(x)
}

#[flux::spec(fn(x: usize{x > 0}) -> usize{v: v < x})]
fn needs_pos(x: usize) -> usize {
    x - 1
}

// The input of the joined signature is inferred from the calls through the pointer
pub fn join_input(b: bool) -> usize {
    let f: fn(usize) -> usize = if b { needs_pos } else { clamp10 };
    f(1)
}

#[flux::spec(fn(n: usize) -> usize{v: v <= 10})]
pub fn join_loop(n: usize) -> usize {
    let mut f: fn(usize) -> usize = clamp10;
    let mut i = 0;
    while i < n {
        f = clamp5;
        i += 1;
    }
    f(n)
}

// Generic fns
fn id<T>(x: T) -> T {
    x
}

pub fn generic_ptr(x: i32) -> i32 {
    let f: fn(i32) -> i32 = id::<i32>;
    f(x)
}

pub fn generic_caller<T>(x: T) -> T {
    let f: fn(T) -> T = id::<T>;
    f(x)
}

// A vector of fn pointers
pub fn vec_of_ptrs(x: usize) -> usize {
    let fs: Vec<fn(usize) -> usize> = vec![clamp10, clamp5];
    fs[0](x)
}
