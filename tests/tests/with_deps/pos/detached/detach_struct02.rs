use flux_rs::*;

pub struct MyStruct(*mut i32);

pub fn new_struct(x: i32) -> MyStruct {
    MyStruct(Box::into_raw(Box::new(x)))
}

pub fn is_pos(z: &MyStruct) -> bool {
    unsafe { *z.0 > 0 }
}

pub fn test() {
    let s = new_struct(10);
    assert(is_pos(&s));
}

#[flux::specs {

    #[opaque]
    #[refined_by(b:bool)]
    struct MyStruct;

    #[trusted]
    fn new_struct(x: i32) -> MyStruct[x > 0];

    #[trusted]
    fn is_pos(&MyStruct[@pos]) -> bool[pos];

}]
const _: () = ();
