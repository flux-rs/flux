fn inc(n: i32) -> i32 {
    n + 1 //~ ERROR refinement type
}

fn id(n: i32) -> i32 {
    n
}

#[flux::specs {
   fn inc(n:i32) -> i32{v: n < v};
   fn id(n:i32) -> i32[n];
}]
const _: () = {};
