#[flux::refined_by(a: int)]
pub struct Range {
    #[flux::field(i32[@a])]
    pub x: i32,
    #[flux::field(i32{v : a < v})]
    pub y: i32,
}

pub fn test(k: i32) -> Range {
    Range { x: k, y: k - 1 } //~ ERROR refinement type error
}
