#[flux::sig(fn(c1: char, c2: char, c3: char) -> char)]
pub fn char00(c1: char, c2: char, c3: char) -> char {
    c1.max(c2).max(c3)
}

#[flux::sig(fn(vec: Vec<char>) -> usize)]
pub fn char01(vec: Vec<char>) -> usize {
    let mut n = 0;
    for c in vec {
        if c.is_alphanumeric() {
            n += 1;
        }
    }
    n
}
