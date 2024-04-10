#![feature(register_tool, box_patterns)]

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

#[flux::sig(fn() -> T requires false)]
fn unreachable<T>() -> T {
    unreachable!()
}

impl Pred {
    // This is failing with a panic
    #[flux::sig(fn(Pred) -> Pred{v : v.nnf})]
    fn into_nnf(self) -> Pred {
        match self {
            Pred::Var(x) => Pred::Var(x),
            Pred::And(p1, p2) => Pred::And(Box::new(p1.into_nnf_()), Box::new(p2.into_nnf_())),
            Pred::Or(p1, p2) => Pred::Or(Box::new(p1.into_nnf_()), Box::new(p2.into_nnf_())),
            Pred::Not(box Pred::Not(p)) => p.into_nnf_(),
            Pred::Not(box Pred::And(p1, p2)) => {
                let p1 = Pred::Not(p1).into_nnf_();
                let p2 = Pred::Not(p2).into_nnf_();
                Pred::Or(Box::new(p1), Box::new(p2))
            }
            Pred::Not(box Pred::Or(p1, p2)) => {
                let p1 = Pred::Not(p1).into_nnf_();
                let p2 = Pred::Not(p2).into_nnf_();
                Pred::And(Box::new(p1), Box::new(p2))
            }
            Pred::Not(p) => Pred::Not(Box::new(p.into_nnf_())),
        }
    }
}

fn main() {}
