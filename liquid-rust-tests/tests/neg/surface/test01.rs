#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(bool, n: i32, m: i32{m >= n}) -> i32{v: v > 1})]
pub fn ref_join(b: bool, n: i32, m: i32) -> i32 { //~ ERROR postcondition might not hold
    let mut x = n;
    let mut y = m;
    let r;
    if b {
        r = &mut x;
    } else {
        r = &mut y;
    }
    *r += 1;
    *r - n
}


#[lr::sig(fn(x: &mut i32{v: 0 <= v}) -> ())]
pub fn test4(x: &mut i32) { 
    *x -= 1; //~ ERROR missmatched type in assignment
}

