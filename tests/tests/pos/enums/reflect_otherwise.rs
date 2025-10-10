use flux_rs::attrs::*;

#[reflect]
pub enum Bob {
    A,
    B,
    C,
}

#[spec(fn (b: Bob) -> bool[b == Bob::A])]
pub fn test_A(b: Bob) -> bool {
    match b {
        Bob::A => true,
        _ => false,
    }
}

#[spec(fn (b: Bob) -> bool[b == Bob::A])]
pub fn test_A_with_macro(b: Bob) -> bool {
    matches!(b, Bob::A)
}

#[spec(fn (b: Bob) -> Bob{v: v != b})]
pub fn test(b: Bob) -> Bob {
    match b {
        Bob::A => Bob::B,
        _ => Bob::A,
    }
}

#[spec(fn (&Bob[@b]) -> Bob{v: v != b})]
pub fn test_ref(b: &Bob) -> Bob {
    match b {
        Bob::A => Bob::B,
        _ => Bob::A,
    }
}

#[spec(fn (&mut Bob[@b]) -> Bob{v: v != b})]
pub fn test_mut_ref(b: &mut Bob) -> Bob {
    match b {
        Bob::A => Bob::B,
        _ => Bob::A,
    }
}

#[spec(fn (&Bob[@b1], &Bob[@b2]) -> bool[b1 == b2])]
fn is_eq(b1: &Bob, b2: &Bob) -> bool {
    match (b1, b2) {
        (Bob::A, Bob::A) => true,
        (Bob::B, Bob::B) => true,
        (Bob::C, Bob::C) => true,
        _ => false,
    }
}
