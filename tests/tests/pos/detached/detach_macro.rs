use flux_rs::{assert, detached_spec};

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

detached_spec! {
  fn watermelon(n:usize) -> usize[n+2];
  fn inc(n:i32) -> i32[n+1];
  fn id(n:i32) -> i32[n];
}
