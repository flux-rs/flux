#[flux::refined_by(n: int)]
pub enum E {
    #[flux::variant({{i32[@n] | n > 0}} -> E[n])]
    Pos(i32),
    #[flux::variant({i32[0]} -> E[0])]
    Zero(i32),
}

#[flux::sig(fn(E[@n], i32[n]) -> i32{v: v > 0})]
pub fn is_zero(_: E, x: i32) -> i32 {
    x + 1 //~ ERROR refinement type
}
