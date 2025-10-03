use flux_attrs::*;

#[extern_spec]
#[flux::refined_by(val: str)]
struct String;

#[extern_spec]
#[assoc(
    fn eq(x: String, y: String) -> bool { x.val == y.val }
)]
impl PartialEq for String {
    #[spec(fn(&String[@s], &String[@t]) -> bool[s.val == t.val] )]
    fn eq(&self, other: &String) -> bool;
}

#[extern_spec]
impl Clone for String {
    #[spec(fn (&String[@s]) -> String[s])]
    fn clone(&self) -> Self;
}

// #[extern_spec]
// impl<'a> From<&'a str> for String {
//     #[spec(fn (&str[@s]) -> String[s])]
//     fn from(s: &'a str) -> String;
// }

#[trusted]
#[spec(fn (&str[@s]) -> String[s])]
pub fn mk_string(s: &str) -> String {
    String::from(s)
}
