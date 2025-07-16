mod bob {
    fn inc(n: i32) -> i32 {
        n + 1
    }

    fn id(n: i32) -> i32 {
        n
    }
}

#[flux::specs {
    mod bob {
        fn inc(n:i32) -> i32{v: n < v};
        fn id(n:i32) -> i32[n];
    }
}]
const test2: () = {};
