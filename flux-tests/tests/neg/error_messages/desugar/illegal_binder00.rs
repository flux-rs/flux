#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(&[i32[@n]]))] //~ ERROR illegal binder
fn hipa(x: &[i32]) {}

#[flux::sig(fn(Option<i32[@n]>))] //~ ERROR illegal binder
fn ira(x: Option<i32>) {}
