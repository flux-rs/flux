#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn({v. i32[1]}))] //~ ERROR sort annotation needed
fn test00(x: i32) {}

#[flux::refined_by(p: int -> bool)]
struct S;

#[flux::sig(fn(S[|a: bool| a]))] //~ ERROR mismatched sorts
fn test01(x: S) {}
