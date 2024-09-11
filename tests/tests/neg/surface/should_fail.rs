// This function doesn't have any errors but it's marked with should_fail so that's bad

#[flux::should_fail]
#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn test01(x: i32) -> i32 { //~ERROR function marked with `#[should_fail]`
    x + 1
}
