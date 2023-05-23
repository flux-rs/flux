#![feature(register_tool)]
#![register_tool(flux)]
#![allow(unused)]

#[flux::refined_by(p: int -> bool)]
struct S;

#[flux::sig(fn(s: S[@p], x: i32{p(x)}))] //~ NOTE inside this specifunction call
fn f(s: S, x: i32) {}

#[flux::sig(fn(s: S[|x| x > 0]))] //~ NOTE this is the condition
fn g(s: S) {
    f(s, 0); //~ ERROR refinement type
             //~| NOTE call site
             //~| NOTE a precondition cannot be proved
}
