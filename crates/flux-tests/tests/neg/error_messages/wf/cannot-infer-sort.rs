#[flux::sig(fn({v. i32[0] | v.f >= 0 }))] //~ERROR sort annotation needed
fn test00(x: i32) {}
