// Implicit casts that lower to &raw const/mut

fn test00(x: &i32) -> *const i32 {
    x
}

fn test01(x: &i32, y: &i32) {
    std::ptr::eq(x, y);
}

fn test02(x: &mut i32) -> *mut i32 {
    x
}
