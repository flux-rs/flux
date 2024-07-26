#[flux::sig(fn(x: (i32)) -> i32)]
fn test00(x: (i32)) -> i32 {
    x
}

#[flux::sig(fn(x: (i32,)) -> i32)]
fn test01(x: (i32,)) -> i32 {
    x.0
}
