use flux_rs::assert;

pub fn inc(n: i32) -> i32 {
    n + 1
}

pub fn id(n: i32) -> i32 {
    n
}

pub fn watermelon(n: usize) -> usize {
    let a = n;
    let b = a + 1;
    let c = b + 1;
    c
}

pub fn test() {
    assert(inc(1) == 2);
    assert(id(1) == 1);
    assert(watermelon(1) == 3);
}

macro_rules! my_spec_block {
    () => {
        #[flux::specs {fn watermelon(n:usize) -> usize[n+2];}]
        const _: usize = 4;

        #[flux::specs {fn inc(n:i32) -> i32[n+1];}]
        const _: usize = 4;

        #[flux::specs {fn id(n:i32) -> i32[n];}]
        const _: () = ();
    };
}

pub fn spec_it_up() {
    my_spec_block!();
}
