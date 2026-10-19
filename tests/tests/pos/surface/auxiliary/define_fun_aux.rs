use flux_attrs::*;

defs! {
    fn inc(x: int) -> int { x + 1 }
    fn inc2(x: int) -> int { inc(inc(x)) }
}
