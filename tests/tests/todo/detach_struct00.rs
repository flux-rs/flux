use flux_rs::assert;

struct MyStruct {
    x: usize,
    y: usize,
}

fn mk_struct(x: usize, y: usize) -> MyStruct {
    MyStruct { x, y } //~ ERROR refinement type
}

fn use_struct(s: MyStruct) {
    assert(s.x < s.y)
}

#[flux::specs {

    struct MyStruct
        refined_by(vx: int, vy: int)
        invariant(vx < vy)
    {
        x: usize[vx],
        y: usize[vy],
    }

}]
const _: () = ();
