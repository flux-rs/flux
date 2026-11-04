type R<T> = Result<T, ()>;

// Refinement on the alias argument mentions an earlier parameter.
#[flux::sig(fn(x: i32, r: R<i32{v: v < x}>))]
pub fn test00(x: i32, r: R<i32>) {
    if let Ok(y) = r {
        assert(y > 1000); //~ ERROR refinement type
    }
}

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}
