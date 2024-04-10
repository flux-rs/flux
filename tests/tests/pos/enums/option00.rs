#[path = "../../lib/option.rs"]
mod option;

#[flux::trusted]
#[flux::sig(fn(i32{v: false}) -> T)]
pub fn never<T>(_: i32) -> T {
    loop {}
}

#[flux::sig(fn(x:Option<T>[true]) -> T)]
pub fn my_unwrap<T>(x: Option<T>) -> T {
    match x {
        Option::Some(v) => v,
        Option::None => never(0),
    }
}

#[flux::trusted]
#[flux::sig(fn(T) -> Option<T>[true])]
fn my_some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

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
