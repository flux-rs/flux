use flux_attrs::*;

#[extern_spec]
#[flux::refined_by(val: str)]
struct String;

#[extern_spec]
#[assoc(
    fn eq(x: String, y: String) -> bool { x.val == y.val }
    fn ne(x: String, y: String) -> bool { x.val != y.val }
)]
impl PartialEq for String {
    #[spec(fn(&String[@s], &String[@t]) -> bool[<String as PartialEq>::eq(s, t)])]
    fn eq(&self, other: &String) -> bool;
}

#[extern_spec]
impl Clone for String {
    #[spec(fn (&String[@s]) -> String[s])]
    fn clone(&self) -> Self;
}
