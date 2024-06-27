#[flux::alias(type Test = Vec<_>)]
type Test = Vec<i32>;

fn test(x: Test) -> Vec<i32> {
    x
}
