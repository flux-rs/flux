#[flux::spec(u32[20])] //~ ERROR specifications on mutable statics are not yet supported
static mut BOB: u32 = 20;
