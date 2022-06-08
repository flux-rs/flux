#![feature(register_tool)]
#![register_tool(flux)]

// We need this right now to not deal with the enum `Some`

#[flux::assume]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[flux::sig(fn() -> i32{v:0 < v})]
pub fn test2() -> i32 { //~ ERROR postcondition might not hold
    let opt = some(0);
    opt.unwrap()
}
