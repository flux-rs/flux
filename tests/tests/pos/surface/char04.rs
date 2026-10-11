// Regression test for ICE when using char literals with escape sequences in specs.

#[flux::sig(fn() -> char['\n'])]
pub fn newline() -> char {
    '\n'
}

#[flux::sig(fn() -> char['\t'])]
pub fn tab() -> char {
    '\t'
}

#[flux::sig(fn() -> char['\r'])]
pub fn carriage_return() -> char {
    '\r'
}

#[flux::sig(fn() -> char['\0'])]
pub fn nul() -> char {
    '\0'
}

#[flux::sig(fn() -> char['\''])]
pub fn single_quote() -> char {
    '\''
}

#[flux::sig(fn() -> char['\"'])]
pub fn double_quote() -> char {
    '\"'
}

#[flux::sig(fn() -> char['\\'])]
pub fn backslash() -> char {
    '\\'
}

#[flux::sig(fn() -> char['\x41'])]
pub fn hex_escape() -> char {
    'A'
}

#[flux::sig(fn() -> char['\u{1F600}'])]
pub fn unicode_escape() -> char {
    '\u{1F600}'
}

#[flux::sig(fn(c: char['\n']) -> bool[true])]
pub fn is_newline(c: char) -> bool {
    c == '\n'
}

#[flux::sig(fn(char[@c]) -> char[c] requires c != '\n' && c != '\t')]
pub fn not_whitespace(c: char) -> char {
    c
}

// `'\x41'` and `'A'` denote the same character
#[flux::sig(fn(char[@c]) -> char['A'] requires c == '\x41')]
pub fn hex_escape_eq_char(c: char) -> char {
    c
}
