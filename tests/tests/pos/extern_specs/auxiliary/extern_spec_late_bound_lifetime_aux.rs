pub fn zero<'a>(_x: &i32) -> &'a i32 {
    &0
}

pub fn f1<'b>(_arg: &u8) -> &'b u8 {
    &42
}

pub fn f2<'a, 'b>(_arg: &'a u8) -> &'b u8 {
    &42
}
