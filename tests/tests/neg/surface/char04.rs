// Regression test for ICE when using char literals with escape sequences in specs.

#[flux::sig(fn() -> char['\n'])]
pub fn newline() -> char {
    '\t' //~ ERROR refinement type
}

#[flux::sig(fn() -> char['\0'])]
pub fn nul() -> char {
    '0' //~ ERROR refinement type
}

#[flux::sig(fn() -> char['\''])]
pub fn single_quote() -> char {
    '\\' //~ ERROR refinement type
}

#[flux::sig(fn() -> char['\x41'])]
pub fn hex_escape() -> char {
    'a' //~ ERROR refinement type
}

#[flux::sig(fn() -> char['\u{1F600}'])]
pub fn unicode_escape() -> char {
    'a' //~ ERROR refinement type
}

#[flux::sig(fn(c: char['\n']) -> bool[true])]
pub fn is_tab(c: char) -> bool {
    c == '\t' //~ ERROR refinement type
}

#[flux::sig(fn(c: char{v: v != '\n'}) -> char['\n'])]
pub fn not_newline(c: char) -> char {
    c //~ ERROR refinement type
}
