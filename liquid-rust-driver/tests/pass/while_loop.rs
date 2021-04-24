#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(n: {int | n >= 0}) -> { v: int | v == n }")]
pub fn id_while(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}
