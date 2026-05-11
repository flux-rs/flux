#[flux::refined_by(a: int)]
struct S {
    #[flux::field(i31[a])] //~ ERROR cannot resolve type `i31` in this scope
    f: i32,
}
