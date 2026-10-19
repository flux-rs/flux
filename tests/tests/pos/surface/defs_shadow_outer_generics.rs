// Names bound by a flux definition shadow the generic parameters of the enclosing item

use flux_attrs::*;

pub fn foo<T, const N: usize>() {
    defs! {
        fn ident<T>(x: T) -> T {
            x
        }

        fn plus_one(N: int) -> int {
            N + 1
        }
    }

    #[spec(fn() -> i32[plus_one(ident(1))])]
    fn test() -> i32 {
        2
    }
}
