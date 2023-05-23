#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(is_atom: bool, nnf: bool)]
#[flux::invariant(is_atom => nnf)]
pub enum Pred {
    #[flux::variant((i32) -> Pred[true, true])]
    Var(i32),
    #[flux::variant(Pred[true, true])]
    True,
    #[flux::variant(Pred[true, true])]
    False,
    #[flux::variant((Box<Pred[@p]>) -> Pred[false, p.is_atom])]
    Not(Box<Pred>),
    #[flux::variant((Box<Pred[@p1]>, Box<Pred[@p2]>) -> Pred[false, p1.nnf && p2.nnf])]
    And(Box<Pred>, Box<Pred>),
    #[flux::variant((Box<Pred[@p1]>, Box<Pred[@p2]>) -> Pred[false, p1.nnf && p2.nnf])]
    Or(Box<Pred>, Box<Pred>),
}

impl Pred {
    #[flux::sig(fn(Pred) -> Pred{v : v.nnf})]
    pub fn into_nnf(self) -> Pred {
        match self {
            Pred::Var(x) => Pred::Var(x),
            Pred::True => Pred::True,
            Pred::False => Pred::False,
            Pred::And(p1, p2) => Pred::And(Box::new(p1.into_nnf()), Box::new(p2.into_nnf())),
            Pred::Or(p1, p2) => Pred::Or(Box::new(p1.into_nnf()), Box::new(p2.into_nnf())),
            Pred::Not(p) => {
                match *p {
                    Pred::Not(p) => p.into_nnf(),
                    Pred::And(p1, p2) => {
                        let p1 = Pred::Not(p1).into_nnf();
                        let p2 = Pred::Not(p2).into_nnf();
                        Pred::Or(Box::new(p1), Box::new(p2))
                    }
                    Pred::Or(p1, p2) => {
                        let p1 = Pred::Not(p1);
                        let p2 = Pred::Not(p2);
                        Pred::And(Box::new(p1), Box::new(p2))
                    }
                    Pred::Var(x) => Pred::Not(Box::new(Pred::Var(x))),
                    Pred::True => Pred::Not(Box::new(Pred::True)),
                    Pred::False => Pred::Not(Box::new(Pred::False)),
                }
            }
        }
    } //~ ERROR refinement type

    #[flux::sig(fn(Pred) -> Pred)]
    pub fn simplify(self) -> Pred {
        match self {
            Pred::Var(x) => Pred::Var(x),
            Pred::True => Pred::True,
            Pred::False => Pred::False,
            Pred::And(p1, p2) => {
                match (p1.simplify(), p2.simplify()) {
                    (Pred::False, _) => Pred::False,
                    (Pred::True, p2) => p2,
                    (p1, p2) => Pred::And(Box::new(p1), Box::new(p2)),
                }
            }
            Pred::Or(p1, p2) => {
                match (p1.simplify(), p2.simplify()) {
                    (Pred::True, _) => Pred::True,
                    (Pred::False, p2) => p2,
                    (p1, p2) => Pred::Or(Box::new(p1), Box::new(p2)),
                }
            }
            Pred::Not(p) => {
                match *p {
                    Pred::False => Pred::True,
                    Pred::True => Pred::False,
                    Pred::Var(x) => Pred::Not(Box::new(Pred::Var(x))),
                    Pred::And(..) => unreachable(), //~ ERROR refinement type
                    Pred::Or(..) => unreachable(),  //~ ERROR refinement type
                    Pred::Not(..) => unreachable(), //~ ERROR refinement type
                }
            }
        }
    }
}

#[flux::sig(fn() -> T requires false)]
fn unreachable<T>() -> T {
    unreachable!()
}
