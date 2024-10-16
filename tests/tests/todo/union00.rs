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
