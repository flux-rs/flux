#![feature(register_tool)]
#![register_tool(flux)]


#[flux::sig(fn(x:i32) -> i32)] //~ ERROR type mismatch
pub fn sob(x: i32) {
    return
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

#[flux::sig(fn(x:i32, y:i32) -> i32)] //~ ERROR arg count mismatch
pub fn baz(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x: &mut i32) -> i32)] //~ ERROR mutability mismatch
pub fn ipa(x: &i32) -> i32 {
    *x + 1
}
