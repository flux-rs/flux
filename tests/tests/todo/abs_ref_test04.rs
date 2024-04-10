#[flux::refined_by(p: (int) -> bool)]
pub enum List {
    #[flux::variant(List[|x| false])]
    Nil,
    #[flux::variant(({i32[@hd] : p(hd)}, Box<List[|x| p(x) && hd <= x]>) -> List[p])]
    Cons(i32, Box<List>),
}

#[flux::sig(fn(head:i32, List[|x| head <= x]) -> List[|x| head <= x ])]
fn cons(head: i32, tail: List) -> List {
    List::Cons(head, Box::new(tail))
}

fn test() -> List {
    cons(1, cons(2, cons(3, List::Nil)))
}
