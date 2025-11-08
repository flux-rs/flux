use flux_rs::{assert, attrs::*};

#[extern_spec]
#[refined_by(s:str)]
struct String;

#[extern_spec]
impl String {
    #[spec(fn(&String[@s]) -> &str[s])]
    fn as_str(s: &String) -> &str;
}

#[trusted]
#[spec(fn (&str[@s]) -> bool[str_prefix_of("cat", s)])]
fn starts_with_cat(s: &str) -> bool {
    s.starts_with("cat")
}

#[trusted]
#[spec(fn (&str[@s]) -> bool[str_suffix_of("cat", s)])]
fn ends_with_cat(s: &str) -> bool {
    s.ends_with("cat")
}

#[trusted]
#[spec(fn (&str[@s]) -> bool[str_contains(s, "cat")])]
fn contains_cat(s: &str) -> bool {
    s.contains("cat")
}

#[trusted]
#[spec(fn (&str[@s1], &str[@s2]) -> String[str_concat(s1, s2)])]
fn concat(a: &str, b: &str) -> String {
    let mut s = String::from(a);
    s.push_str(b);
    s
}

#[spec(fn (&str[@a], &{str[@b] | a == b}))]
fn require_eq(_x: &str, _y: &str) {}

pub fn test() {
    assert(starts_with_cat("catnap"));
    assert(!starts_with_cat("dognap"));
    assert(ends_with_cat("wildcat"));
    assert(!ends_with_cat("wilddog"));
    assert(contains_cat("concatenate"));
    assert(!contains_cat("dogmatic"));
}

pub fn test_concat() {
    let cat = "cat";
    let dog = "dog";
    let catdog = "catdog";
    let combined = concat(cat, dog);
    require_eq(combined.as_str(), catdog);
}
