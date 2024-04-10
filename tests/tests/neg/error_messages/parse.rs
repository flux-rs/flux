#[flux::opaque]
struct S {
    #[flux::field(i32[0])] //~ ERROR opaque struct can't have refined fields
    f: i32,
}

#[flux::refined_by(x: int)]
enum E {
    A(i32), //~ ERROR missing variant
}
