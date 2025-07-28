use flux_rs::assert;

pub struct MyStruct {
    x: usize,
    y: usize,
}

pub fn mk_struct(x: usize, y: usize) -> MyStruct {
    MyStruct { x, y } //~ ERROR refinement type
}

pub fn use_struct(s: MyStruct) {
    assert(s.x < s.y)
}

#[flux::specs {

    #[refined_by(vx: int, vy: int)]
    #[invariant(vx < vy)]
    struct MyStruct {
        x: usize[vx],
        y: usize[vy],
    }

}]
const _: () = ();
