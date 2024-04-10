#[flux::alias(type Gt(x: int) = i32{v: v > x})]
type Gt = i32;

#[flux::sig(fn(Gt))] //~ ERROR this type alias takes 1 early bound argument
fn test00(x: Gt) {}

fn test01(x: Gt) {} //~ ERROR this type alias takes 1 early bound argument
