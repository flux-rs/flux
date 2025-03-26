use flux_rs::attrs::*;

defs! {
    fn test00() -> int {
        1(0) //~ ERROR expression not allowed in this position
    }

    fn test01() -> int {
        <Self as Trait>::assoc + 1 //~ ERROR expression not allowed in this position
    }
}
