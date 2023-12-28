// use flux_rs::extern_spec;

// #[extern_spec]
// #[flux::refined_by(is_some: bool)]
// enum Option<T> {}

// #[extern_spec]
// #[flux::refined_by(is_some: bool)]
// enum Option<T> {

// }

// // Programmer writes
// #[extern_spec]
// #[flux::refined_by(b:bool)]
// pub enum Option<T> {
//     #[flux::variant(Option<T>[false])]
//     None,
//     #[flux::variant({T} -> Option<T>[true])]
//     Some(T),
// }

// Compiler generates
#[flux::extern_spec]
#[allow(unused, dead_code)]
#[flux::refined_by(b:bool)]
pub enum __FluxExternEnumOption<T> {
    #[flux::variant(Option<T>[false])]
    None,
    #[flux::variant({T} -> Option<T>[true])]
    Some(T),
    // #[flux::variant(Option<T>)]
    FluxExternEnumFake(Option<T>),
}

#[flux::trusted]
#[flux::sig(fn(x:Option<T>[true]) -> T)]
fn my_unwrap<T>(x: Option<T>) -> T {
    match x {
        Option::Some(v) => v,
        Option::None => panic!(),
    }
}

#[flux::trusted]
#[flux::sig(fn(T) -> Option<T>[true])]
fn my_some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[flux::trusted]
#[flux::sig(fn() -> Option<T>[false])]
fn my_none<T>() -> Option<T> {
    Option::None
}

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test1() {
    let x = my_some(42);
    let y = my_unwrap(x);
    assert(y == 42);
}

pub fn test2() {
    let x: Option<i32> = my_none();
    let y = my_unwrap(x); //~ ERROR refinement type
    assert(y == 42);
}
