#![feature(register_tool)]
#![register_tool(flux)]

use flux_attrs_proc_macros::extern_spec;

#[extern_spec]
#[flux::refined_by(len: int)]
struct String;

#[extern_spec]
impl String {
    #[flux::sig(fn() -> String[0])]
    fn new() -> String;

    #[flux::sig(fn(&String[@n]) -> usize[n])]
    fn len(s: &String) -> usize;

    #[flux::sig(fn(&String[@n]) -> bool[n == 0])]
    fn is_empty(s: &String) -> bool;

    #[flux::sig(fn(s: &strg String[@n], char) ensures s: String[n+1])]
    fn push(s: &mut String, c: char);

    #[flux::sig(fn(s: &strg String[@n]) -> Option<char>
                requires n > 0
                ensures s: String[n-1])]
    fn pop(s: &mut String) -> Option<char>;

    #[flux::sig(fn(&String[@n]) -> &[u8][n])]
    fn as_bytes(s: &String) -> &[u8];
}


#[extern_spec]
impl<T> [T] {
    #[flux::sig(fn(&[T][@n]) -> usize[n])]
    fn len(v: &[T]) -> usize;

    #[flux::sig(fn(&[T][@n]) -> bool[n == 0])]
    fn is_empty(v: &[T]) -> bool;
}

#[flux::sig(fn(bool[@b]) requires b)]
fn assert_true(_: bool) {
}

fn test_string() {
    let mut s = String::new();
    s.push('h');
    s.push('i');
    s.pop();
    s.pop();
    assert_true(s.as_bytes().is_empty());
    assert_true(!s.as_bytes().is_empty()); //~ ERROR precondition
    s.pop(); //~ ERROR precondition
}
