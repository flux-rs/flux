// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: fn(u32[@b0], u32[@b0_1], (u32[@b0_2],))
#![flux::opts(check_overflow = "strict")]

#[flux::sig(fn(u32[@b0], u32[@b0_1], (u32,)) -> u32)]
fn add(x: u32, y: u32, (b0,): (u32,)) -> u32 {
    x + y + b0 //~ ERROR arithmetic operation may overflow
    //~^ ERROR arithmetic operation may overflow
}
