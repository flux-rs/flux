#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(f32) -> f32)]
pub fn float00(x: f32) -> f32 {
    let y = x + 0.1;
    x - y
}
