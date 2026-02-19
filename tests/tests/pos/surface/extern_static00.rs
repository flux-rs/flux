extern "C" {
    static _szero: *const u32;
}

#[flux::trusted(reason = "deref raw static")]
fn foo(n: i32) -> u32 {
    let x = unsafe { *_szero };
    x
}
