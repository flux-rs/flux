use flux_rs::attrs::*;


#[spec(fn() -> i32{v:0<=v})]
pub fn test() -> i32 {
    let mut i = 0;
    let mut res = 0;
    while i < 100 {
        i += 1;
        res += 1;
    }
    res
}

