pub struct MyStruct(i32);

fn foo() -> MyStruct {
    let s = MyStruct(10);
    s
}

pub fn test() -> i32 {
    let s = foo();
    s.0
}

#[flux::specs {

    #[refined_by(inner:int)]
    struct MyStruct(i32[inner])

    fn foo() -> MyStruct[10];
    fn test() -> i32[10];
}]
const _: () = ();
