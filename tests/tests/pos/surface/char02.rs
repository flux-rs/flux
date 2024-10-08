#[flux::sig(fn() -> char['a'])]
pub fn char00() -> char {
    'a'
}

#[flux::sig(fn(c: char{v: 'a' <= v && v <= 'z'}) -> bool[true])]
pub fn lowercase(c: char) -> bool {
    'c' == 'c'
}

pub fn TESTlowercase(c: char) -> bool {
    'c' == 'c'
}