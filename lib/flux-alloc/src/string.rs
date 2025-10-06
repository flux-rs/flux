use flux_attrs::*;

#[extern_spec]
#[flux::refined_by(val: str)]
struct String;

#[extern_spec]
#[assoc(
    fn is_eq(x: String, y: String, res: bool) -> bool { res <=> (x.val == y.val) }
    fn is_ne(x: String, y: String, res: bool) -> bool { res <=> (x.val != y.val) }
)]
impl PartialEq for String {
    #[spec(fn(&String[@s], &String[@t]) -> bool[s == t])]
    fn eq(&self, other: &String) -> bool;
}

#[extern_spec]
#[assoc(fn cloned(old: Self, new: Self) -> bool { old == new } )]
impl Clone for String {
    #[spec(fn (&String[@s]) -> String[s])]
    fn clone(&self) -> Self;
}

#[trusted]
#[spec(fn(&str[@s]) -> String[s])]
pub fn mk_string(s: &str) -> String {
    s.to_string()
}
