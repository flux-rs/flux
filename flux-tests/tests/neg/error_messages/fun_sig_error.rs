#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x:&mut i32[@n]) ensures x: i32[n+1])] //~ ERROR cannot resolve
pub fn say_strng(x: &mut i32) {
    *x += 1;
    return;
}

#[flux::sig(fn(x:i32) -> i32)] //~ ERROR type mismatch
pub fn sob(x: i32) {
    return;
}

#[flux::sig(fn(x:i32) -> i32)] //~ ERROR type mismatch
pub fn foo(x: bool) -> i32 {
    if x {
        1
    } else {
        2
    }
}

#[flux::sig(fn(x:i32) -> i32)] //~ ERROR type mismatch
pub fn bar(x: i32) -> bool {
    x > 0
}

#[flux::sig(fn(x:Vec<i32>) -> i32)] //~ ERROR cannot resolve
pub fn boo(x: i32) -> bool {
    x > 0
}

#[flux::sig(fn(x:Option<i32>) -> i32)] //~ ERROR type mismatch
pub fn goo(x: i32) -> Option<i32> {
    Some(x)
}

#[flux::sig(fn(x:i32, y:i32) -> i32)] //~ ERROR argument count mismatch
pub fn baz(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x: &mut i32) -> i32)] //~ ERROR mutability mismatch
pub fn ipa(x: &i32) -> i32 {
    *x + 1
}

#[flux::sig(fn())] //~ ERROR return type mismatch
fn ris() -> i32 {
    0
}

type A<'a> = &'a [i32];

#[flux::sig(fn())]
fn dipa(x: A) {} //~ ERROR unsupported function signature

#[flux::sig(fn(&[i32[@n]]))] //~ ERROR illegal binder
fn hipa(x: &[i32]) {}

#[flux::sig(fn(Option<i32[@n]>))] //~ ERROR illegal binder
fn ira(x: Option<i32>) {}

#[flux::sig(fn(x: f32))] //~ ERROR type mismatch
fn hefe(f: &mut f32) {}

#[flux::sig(fn(x: &mut f32))] //~ ERROR type mismatch
fn quad(f: f32) {}
