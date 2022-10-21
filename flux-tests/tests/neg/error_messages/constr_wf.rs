#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

#[flux::sig(fn(x: &strg i32[@n]))] //~ ERROR missing ensures clause
fn inc_1(x: &mut i32) {
    *x += 1;
}

#[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n + 2], x: i32 [n + 1])] //~ ERROR an ensures clause already exists
fn inc1(x: &mut i32) {
    *x += 1;
}
