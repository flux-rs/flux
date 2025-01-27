#[flux::alias(type Gt(x: int)[v: int] = { i32[v] | v > x })]
type Gt = i32;

#[flux::sig(fn(Gt))] //~ ERROR type alias takes 1 generic refinement argument
fn test00(x: Gt) {}

fn test01(x: Gt) {} //~ ERROR type alias takes 1 generic refinement argument
