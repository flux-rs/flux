#[flux::refined_by(b: int)]
pub enum E2 {
    #[flux::variant((i32[@n]) -> E2[@n])] //~ ERROR illegal binder
    A(i32),
}
