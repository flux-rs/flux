use flux_rs::assert;

pub fn inc(n: i32) -> i32 {
    n + 1
}

pub fn id(n: i32) -> i32 {
    n
}

pub fn test() {
    assert(inc(1) == 2);
    assert(id(1) == 1);
}

#[flux::specs {

   fn inc(n:i32) -> i32[n+1];

   fn id(n:i32) -> i32[n];

}]
const _: () = ();
