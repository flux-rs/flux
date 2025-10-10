use flux_rs::attrs::*;

#[reflect]
pub enum Bob {
    A,
    B,
    C,
}

#[spec(fn (b: Bob) -> Bob{v: v != b})]
fn test(b: Bob) -> Bob {
    match b {
        Bob::A => Bob::B,
        _ => Bob::A,
    }
}
