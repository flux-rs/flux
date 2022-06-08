#![feature(register_tool)]
#![register_tool(flux)]

// We need this right now to not deal with the enum `Some`

#[flux::assume]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[flux::sig(fn() -> i32{v:10 <= v})]
pub fn test2() -> i32 {
    let opt = some(12);
    opt.unwrap()
}
