use flux_rs::assert;

#[flux_rs::refined_by(vx: int, vy: int)]
pub struct MyStruct {
    #[flux_rs::field(usize[vx])]
    x: usize,
    #[flux_rs::field(usize[vx])]
    y: usize,
}

pub fn mk_struct(x: usize, y: usize) -> MyStruct {
    if x < y { MyStruct { x, y } } else { MyStruct { x: y, y: x } }
}

pub fn use_struct(s: MyStruct) {
    assert(s.x <= s.y)
}

#[flux::specs {

    struct MStruct//~ ERROR unresolved identifier `MStruct`
        refined_by(vx: int, vy: int)
        invariant(vx <= vy)
    {
        x: usize[vx],
        y: usize[vy],
    }

}]
const _: () = ();
