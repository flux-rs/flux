// This function has an error
// but it's marked as should_fail so that ok.
// flux would yell if instead it verified!

#[flux::should_fail]
#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn test00(x: i32) -> i32 {
    x + 2
}
