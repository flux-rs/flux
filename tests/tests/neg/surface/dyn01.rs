#![allow(unused)]

// ------------------------------------------------------

trait Shape {
    #[flux::sig(fn(self: _) -> i32{v: 0 <= v})]
    fn vertices(&self) -> i32;
}

// ------------------------------------------------------

struct Circle {}

impl Shape for Circle {
    fn vertices(&self) -> i32 {
        0
    }
}

// ------------------------------------------------------

#[flux::sig(fn(shape: _) -> i32{v: 0 <= v})]
fn count(shape: &dyn Shape) -> i32 {
    shape.vertices()
}

#[flux::sig(fn(shape: _) -> i32{v: 10 <= v})]
fn count_bad(shape: &dyn Shape) -> i32 {
    shape.vertices() //~ ERROR: refinement type
}

fn main() {
    let c = Circle {};
    count(&c);
    count_bad(&c);
}
