#![feature(register_tool)]
#![register_tool(lr)]

// We need this right now to not deal with the enum `Some`

#[lr::assume]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[lr::sig(fn() -> i32{v:0 < v})]
pub fn test2() -> i32 {
    let opt = some(0);
    opt.unwrap() //~ ERROR postcondition might not hold
}
