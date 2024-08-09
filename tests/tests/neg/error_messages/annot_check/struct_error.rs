struct S1 {
    #[flux::field(i64)] //~ ERROR incompatible refinement annotation
    x: i32,
    y: i64,
}

struct S2 {
    x: Box<S2>,
}
