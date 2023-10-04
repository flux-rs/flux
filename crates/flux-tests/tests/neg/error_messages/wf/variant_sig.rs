#[flux::refined_by(b: int)]
pub enum E2 {
    #[flux::variant((i32[true]) -> E2[0])] //~ ERROR mismatched sorts
    A(i32),
    #[flux::variant(E2[true])] //~ ERROR mismatched sorts
    B,
}
