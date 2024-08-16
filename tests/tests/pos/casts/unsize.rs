#[flux::sig(fn(&[u8{v: v > 0}; 3]) -> &[u8{v: v > 0}][3])]
fn test00(x: &[u8; 3]) -> &[u8] {
    x
}

#[flux::sig(fn(Box<[u8{v: v > 0}; 3]>) -> Box<[u8{v: v > 0}][3]>)]
fn test01(x: Box<[u8; 3]>) -> Box<[u8]> {
    x
}
