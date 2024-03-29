// Test definition and checking of const and qualifiers

#![flux::defs {
    qualifier Sub2(x: int, a: int, b:int) { x == a - b }
}]

#[flux::refined_by(len: int)]
pub enum List {
    #[flux::variant(List[0])]
    Nil,
    #[flux::variant((i32, Box<List[@n]>) -> List[n+1])]
    Cons(i32, Box<List>),
}

impl List {
    #[flux::sig(fn(&List[@n]) -> usize[n])]
    fn len_const_memory(&self) -> usize {
        let mut len = 0;
        let mut cur = self;
        while let List::Cons(_, tl) = cur {
            len += 1;
            cur = tl;
        }
        len
    }
}

#[flux::refined_by(x: int)]
pub enum Thing {
    #[flux::variant(Thing[1])]
    One,
    #[flux::variant(Thing[2])]
    Two,
    #[flux::variant(Thing[3])]
    Three,
}

#[flux::sig(fn(&Thing[@x]) -> i32[x])]
pub fn test1(l: &Thing) -> i32 {
    match l {
        Thing::Two => 2,
        Thing::Three => 3,
        _ => 1,
    }
}

#[flux::sig(fn(&Thing[@x]) -> i32[x])]
pub fn test2(l: &Thing) -> i32 {
    match l {
        Thing::One => 1,
        Thing::Three => 3,
        _ => 2,
    }
}

#[flux::sig(fn(&Thing[@x]) -> i32[x])]
pub fn test3(l: &Thing) -> i32 {
    match l {
        Thing::One => 1,
        Thing::Two => 2,
        _ => 3,
    }
}
