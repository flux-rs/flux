pub fn foo(z: &mut Option<i32>) -> i32 {
    match z {
        Some(n) => *n,
        None => 0,
    }
}
