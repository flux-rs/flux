use flux_rs::{assert, attrs::*};

extern crate flux_core;

#[flux::trusted]
#[spec(fn(i32{v: false}) -> T)]
pub fn never<T>(_: i32) -> T {
    loop {}
}

#[spec(fn(x:Option<T>[true]) -> T)]
pub fn my_unwrap<T>(x: Option<T>) -> T {
    match x {
        Option::Some(v) => v,
        Option::None => never(0),
    }
}

#[spec(fn(T) -> Option<T>[true])]
fn my_some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

pub fn test1() {
    let x = my_some(42);
    let y = my_unwrap(x);
    assert(y == 42);
}

pub fn test3() {
    let x = Option::Some(42);
    let y = my_unwrap(x);
    assert(y == 42);
}

pub fn test_opt_specs() {
    let a = Some(42);
    assert(a.is_some());
    let b: Option<i32> = None;
    assert(b.is_none());
    let c = a.unwrap();
    assert(c == 42);
}

#[spec(fn (numerator: u32, denominator: u32) -> Option<u32[numerator / denominator]>[denominator != 0])]
pub fn safe_div(numerator: u32, denominator: u32) -> Option<u32> {
    if denominator == 0 { None } else { Some(numerator / denominator) }
}

pub fn test_safe_div() {
    let res = safe_div(42, 2).unwrap();
    assert(res == 21);
}
