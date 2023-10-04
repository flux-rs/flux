struct S;

#[flux::sig(fn(x: S, y: i32))]
fn test00(x: S, y: i32) {}

fn test01() {
    test00(S, 0)
}
