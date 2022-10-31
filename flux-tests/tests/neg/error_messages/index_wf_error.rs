#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by()]
pub struct Chair {
    #[flux::field(i32{v: 0 < v})]
    pub x: i32,
}

#[flux::sig(fn () -> Chair[0])] //~ ERROR this type takes 0 refinement parameters but 1 was found
pub fn mk_chair() -> Chair {
    Chair { x: 0 }
}
