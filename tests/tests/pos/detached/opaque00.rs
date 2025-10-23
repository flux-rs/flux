pub struct MyStruct0 {
    pub inner: i32,
}

// 1. Parse `opaque`
#[flux::specs {

    #[opaque]
    #[refined_by(inner:int)]
    struct MyStruct0 {
        inner: i32[inner],
    }

}]
const _: () = ();
