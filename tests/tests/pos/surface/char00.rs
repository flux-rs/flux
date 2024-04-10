pub fn char00() -> char {
    'a'
}

pub fn char01(x: u32) -> char {
    if let Some(c) = char::from_u32(x) {
        c
    } else {
        'a'
    }
}
