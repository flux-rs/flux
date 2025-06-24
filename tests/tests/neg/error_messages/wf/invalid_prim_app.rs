use flux_rs::attrs::*;

#[spec(fn () ensures [<<](1, 2) == [<<](1, 2))]
pub fn test() {}
