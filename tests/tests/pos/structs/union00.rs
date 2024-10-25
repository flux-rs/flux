#![allow(unused)]

pub union Silly {
    this: i32,
    that: bool,
}

pub fn bob(s: Silly) -> i32 {
    unsafe { s.this }
}

pub fn glob(s: Silly) -> bool {
    unsafe { s.that }
}

pub fn new_this(v: i32) -> Silly {
    Silly { this: v }
}

pub fn new_that(b: bool) -> Silly {
    Silly { that: b }
}
