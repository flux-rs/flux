pub union Silly {
    this: i32,
    that: u32,
}

pub fn bob(s: Silly) -> i32 {
    unsafe { s.this }
}

pub fn glob(s: Silly) -> u32 {
    unsafe { s.that }
}

pub fn new_this(v: i32) -> Silly {
    Silly { this: v }
}

pub fn new_that(v: u32) -> Silly {
    Silly { that: v }
}
