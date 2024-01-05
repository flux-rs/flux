#[flux::refined_by()]
pub struct Chair {
    #[flux::field(i32{v: 0 < v})]
    pub x: i32,
}

#[flux::refined_by(x:int, y:int)]
pub struct Pair {
    #[flux::field(i32[x])]
    pub x: i32,
    #[flux::field(i32[y])]
    pub y: i32,
}

#[flux::sig(fn(Pair[@p,@q,@r]) -> i32[p])] //~ ERROR this type takes 2 refinement arguments but 3 were found
pub fn mytuple1(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(Pair[@p]) -> i32[p])] //~ ERROR mismatched sorts
pub fn mytuple2(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(i32[@n]) -> i32[n.x])] //~ ERROR `int` is a primitive sort
pub fn myint1(x: i32) -> i32 {
    x
}

#[flux::sig(fn(f: f32) -> i32[f.x])] //~ ERROR no field `x` on sort `()`
fn ris(f: f32) -> i32 {
    0
}

#[flux::sig(fn(f: f32) -> i32[f])] //~ ERROR mismatched sorts
fn ipa(f: f32) -> i32 {
    0
}

// We should improve this error message. Mismatched sorts is a bit confusing here
#[flux::sig(fn () -> Chair[0])] //~ ERROR mismatched sorts
pub fn mk_chair() -> Chair {
    Chair { x: 0 }
}

#[flux::sig(fn(c: Chair) -> i32[c.a])] //~ ERROR no field `a` on sort `Chair`
pub fn use_chair(c: Chair) -> i32 {
    c.x
}

#[flux::sig(fn(f32{v : v > 0}) -> i32[0])] //~ ERROR mismatched sorts
fn ira(f: f32) -> i32 {
    0
}

// We should improve this error message it currently says expected int but found err
#[flux::sig(fn(x: T) -> i32[x])] //~ ERROR mismatched sorts
fn generic<T>(x: T) -> i32 {
    0
}
