// Test that we at least support mentioning function pointers

pub struct Struct {
    f: fn(i32) -> i32,
}

pub fn test00(x: fn(i32) -> i32) {}

pub fn test01(x: Vec<fn(i32) -> i32>) {}
