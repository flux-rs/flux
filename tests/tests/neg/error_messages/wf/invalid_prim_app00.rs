use flux_attrs::*;

#[spec(fn () ensures [<<](1, 2))] //~ ERROR expression not allowed in this position
pub fn test() {}
