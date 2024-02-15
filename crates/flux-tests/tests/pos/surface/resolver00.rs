#[flux::sig(fn(x: std::vec::Vec<i32>))]
fn test00(x: Vec<i32>) {}

#[flux::sig(fn(x: Vec<i32>))]
fn test01(x: std::vec::Vec<i32>) {}
