fn blah(n: i32) -> i32 {
    n + 1
}

mod bob {
    fn inc(n: i32) -> i32 {
        n + 1
    }

    fn id(n: i32) -> i32 {
        n
    }
}

#[flux::specs {

    fn blah(n:i32) -> i32[n+1]

    mod bob {

        fn inc(n:i32) -> i32{v: n < v}

        fn id(n:i32) -> i32[n]
    }

}]
const _: () = ();
