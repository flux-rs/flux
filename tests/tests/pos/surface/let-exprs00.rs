use flux_rs::attrs::*;

defs! {
    fn times2(x: int) -> int {
        x * 2
    }

    fn test(x: int) -> int {
        let y = times2(x);
        let z = times2(y);
        z * z * y
    }
}

#[sig(fn() -> i32[test(10)])]
fn test() -> i32 {
    32000
}
