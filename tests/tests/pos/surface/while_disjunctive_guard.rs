#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::sig(fn(u32{x: x == 0 || x == 2}))]
fn test_while(mut x: u32) {
    while x != 2 {
        assert(x != 2);
        assert(x == 0);
        x = 2;
    }
}
