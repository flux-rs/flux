#[flux::refined_by(x: int, y: int)]
struct S {
    #[flux::field(i32[x])]
    x: i32,
    #[flux::field(i32[y])]
    y: i32,
}

// We are testing that the adt sort `S` is correctly encoded into a tuple, i.e., that the fixpoint
// constraint will contain (something like) `forall x: Tuple2 int int. tuple2$0 x == tuple2$0 x && tuple2$1 x == tuple2$1`
#[flux::sig(fn() requires forall r: S. r.x == r.x && r.y == r.y)]
fn test00() {}

fn test01() {
    test00();
}
