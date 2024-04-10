#[flux::opaque]
struct S {
    #[flux::field(i32[0])] //~ ERROR opaque struct can't have refined fields
    x: i32,
}
