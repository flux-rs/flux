#![allow(unused)]

#[flux::refined_by(b: B)]
struct A;

#[flux::refined_by(a: A)]
struct B;

fn main() {}
