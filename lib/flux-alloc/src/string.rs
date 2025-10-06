use flux_attrs::*;

#[extern_spec]
#[flux::refined_by(val: str)]
struct String;

#[extern_spec]
#[assoc(
    fn eq(x: String, y: String) -> bool { x.val == y.val }
)]
impl PartialEq for String {
    #[spec(fn(&String[@s], &String[@t]) -> bool[<String as PartialEq>::eq(s, t)])]
    fn eq(&self, other: &String) -> bool;
}

#[extern_spec]
impl Clone for String {
    #[spec(fn (&String[@s]) -> String[<String as Clone>::cloned(s)])]
    fn clone(&self) -> Self;
}

#[trusted]
#[spec(fn(&str[@s]) -> String[s])]
pub fn mk_string(s: &str) -> String {
    s.to_string()
}
