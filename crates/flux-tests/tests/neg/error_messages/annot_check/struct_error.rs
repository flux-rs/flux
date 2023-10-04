struct S1 {
    #[flux::field(i64)] //~ ERROR invalid refinement annotation
    x: i32,
    y: i64,
}

struct S2 {
    x: Box<S2>,
}
