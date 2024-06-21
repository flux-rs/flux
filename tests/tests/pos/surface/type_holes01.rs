// Type holes in structts and enums

pub struct S {
    #[flux::field(Option<_>)]
    x: Option<i32>,
}

pub fn test_s(s: S) -> Option<i32> {
    s.x
}

pub enum E {
    #[flux::variant((_) -> E)]
    A(i32),
}

pub fn test_e(e: E) -> i32 {
    match e {
        E::A(x) => x,
    }
}
