#[flux::alias(type Gt(x: bool)[v: int] = { i32[v] | v > x })] //~ ERROR mismatched sorts
type Gt = i32;
