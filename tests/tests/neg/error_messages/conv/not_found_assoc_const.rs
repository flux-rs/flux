use flux_rs::attrs::*;

#[spec(fn(x: i32 { x == i32::BAD }))] //~ ERROR associated constant not found
fn test00(x: i32) {}
