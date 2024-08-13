#[flux::sig(fn(x: &strg i32) ensures x: i64)] //~ERROR incompatible refinement
fn test00(x: &mut i32) {}
