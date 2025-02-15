extern "C" {
    pub fn test00(x: i32) -> i32;
}

fn test01() {
    let x = unsafe { test00(0) };
}
