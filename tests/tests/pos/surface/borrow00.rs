struct S {
    x: i32,
}

impl S {
    fn get(&self) -> i32 {
        self.x
    }
}

fn test00(s: &S, x: i32) {}

fn test01() {
    let s = S { x: 0 };
    test00(&s, s.get());
}
