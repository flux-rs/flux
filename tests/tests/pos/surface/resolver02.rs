// Test we resolve flux defs inside their parent module
mod my_module {
    use flux_rs::*;

    defs! {
        fn is_pos(x: MyStruct) -> bool {
            x.n > 0
        }
    }

    #[refined_by(n: int)]
    struct MyStruct {
        #[field(i32[n])]
        f: i32,
    }

    #[sig(fn(MyStruct{v: is_pos(v)}) -> i32{v: v > 0})]
    fn test00(x: MyStruct) -> i32 {
        x.f
    }
}

// Test the same but where the parent is an item with a block
const _: () = {
    use flux_rs::*;

    defs! {
        fn is_pos(x: MyStruct) -> bool {
            x.n > 0
        }
    }

    #[refined_by(n: int)]
    struct MyStruct {
        #[field(i32[n])]
        f: i32,
    }

    #[sig(fn(MyStruct{v: is_pos(v)}) -> i32{v: v > 0})]
    fn test00(x: MyStruct) -> i32 {
        x.f
    }
};
