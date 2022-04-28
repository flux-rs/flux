#![feature(register_tool)]
#![register_tool(lr)]

// We need this right now to not deal with the enum `Some`

#[lr::assume]
#[lr::sig(fn(T) -> Option<T>)]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[lr::sig(fn() -> i32{v:0 < v})]
pub fn test2() -> i32 { //~ ERROR postcondition might not hold
    let opt = some(0);
    opt.unwrap()
}
