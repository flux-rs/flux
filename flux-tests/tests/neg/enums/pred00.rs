#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(is_var: bool, nnf: bool)]
#[flux::invariant(is_var => nnf)]
pub enum Pred {
    #[flux::variant((i32) -> Pred[true, true])]
    Var(i32),
    #[flux::variant((Box<Pred[@p]>) -> Pred[false, p.is_var])]
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
                }
            }
        }
    } //~ ERROR postcondition
}
