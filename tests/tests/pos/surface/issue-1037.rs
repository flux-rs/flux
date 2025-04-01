struct S1 {
    x: i32,
}

struct S2 {
    s1: S1,
}

impl S2 {
    fn new() -> Self {
        todo!()
    }
}

fn test() {
    if true {
        let s2 = S2::new();
        s2.s1.x;
    } else {
        // the fold/unfold analysis inserts an unfold at `s2.s1` at the end of this branch but the
        // place has type uninit
    }
}
