#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

#[flux::opaque]
#[flux::refined_by(a: int)]
struct Struct;

#[flux::sig(fn(s: &mut Struct{v : v > 0}))]
fn take_mut(s: &mut Struct) {}

#[flux::assume]
#[flux::sig(fn(s: &strg Struct[@n]) ensures s: Struct[n + 1])]
fn take_strg(s: &mut Struct) {}

#[flux::sig(fn(s: &strg Struct{v : v >= 0}) ensures s: Struct{v : v > 0})]
fn test00(s: &mut Struct) {
    take_strg(s);
    loop {
        take_mut(s);
        take_strg(s);
    }
}

#[flux::sig(fn(s: &strg Struct{v : v > 0}) ensures s: Struct)]
fn test01(s: &mut Struct) {
    loop {
        take_mut(s);
    }
}
