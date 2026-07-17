#[flux::refined_by(a: int)]
struct S {
    #[flux::field(i31[a])] //~ ERROR cannot find type `i31` in this scope
    f: i32,
}
