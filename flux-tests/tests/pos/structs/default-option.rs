#![feature(register_tool)]
#![register_tool(lr)]

// We need this right now to not deal with the enum `Some`

#[lr::assume]
fn some<T>(x: T) -> Option<T> {
    Option::Some(x)
}

#[lr::sig(fn() -> i32{v:10 <= v})]
pub fn test2() -> i32 {
    let opt = some(12);
    opt.unwrap()
}
