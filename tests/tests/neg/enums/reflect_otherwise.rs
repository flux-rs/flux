use flux_rs::attrs::*;

#[reflect]
pub enum Bob {
    A,
    B,
    C,
}

#[spec(fn (&Bob[@b1], &Bob[@b2]) -> bool[b1 == b2])]
fn is_eq(b1: &Bob, b2: &Bob) -> bool {
    match (b1, b2) {
        (Bob::A, Bob::A) => true,
        (Bob::B, Bob::B) => true,
        _ => false, //~ ERROR refinement type error
    }
}
