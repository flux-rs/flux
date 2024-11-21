#[flux::refined_by(x: int, y: int)]
pub enum E {
    #[flux::variant(E[0, 1])]
    Variant1,
    #[flux::variant(E[1, 2])]
    Variant2,
    #[flux::variant(E[2, 3])]
    Variant3,
}

#[flux::sig(fn (e: E[@old_enum]) -> E[{ x: 1, y: 2 }])]
fn f(e: E) -> E {
    E::Variant2
}
