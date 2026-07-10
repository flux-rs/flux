#[flux::refined_by(x: int, y: int)]
pub struct Foo {
    #[flux::field({usize[x]| x < 100})]
    pub x: usize,
    #[flux::field({usize[y]| y < 100})] //~ NOTE this is the condition
    pub y: usize,
}

pub fn test(a: &mut Foo) {
    a.y += 1;
} //~ ERROR type invariant may not hold
