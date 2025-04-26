#[flux::sig(fn(x: &i32[@n]) ensures x: i32[n+1])] //~ ERROR syntax error
pub fn test00(x: &mut i32) {
    *x += 1;
    return;
}

#[flux::sig(fn(x: &i32[@n]) ensures x: i32[n+1])] //~ ERROR syntax error
pub fn test01(x: &i32) {}
