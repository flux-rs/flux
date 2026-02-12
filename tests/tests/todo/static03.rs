extern "C" {
    static _szero: *const u32;
}

fn foo(n: i32) -> u32 {
    let x = unsafe { *_szero };
    x
}
