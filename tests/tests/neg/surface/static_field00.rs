// The initializer of a static without a spec must satisfy the field specs of its type,
// as they are assumed when reading from the static.
#[flux::refined_by()]
pub struct Pos {
    #[flux::field(usize{v: v > 0})]
    x: usize,
}

static BADPOS: Pos = Pos { x: 0 }; //~ ERROR refinement type

#[flux::spec(fn() -> usize{v: v > 0})]
pub fn read_bad() -> usize {
    BADPOS.x
}
