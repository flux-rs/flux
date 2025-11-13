// A port from https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.17/LIPIcs.ECOOP.2023.17.pdf

use std::collections::HashMap;

use flux_rs::attrs::*;

#[reflect]
enum ExprLbl {
    Var,
    Cst,
    Not,
    Or,
    And,
    Xor,
}

#[refined_by(s: Set<ExprLbl>)]
enum Expr {
    #[variant((i32) -> Expr[#{ExprLbl::Var}])]
    Var(i32),
    #[variant((bool) -> Expr[#{ExprLbl::Cst}])]
    Cst(bool),
    #[variant((Box<Expr[@s]>) -> Expr[s | #{ExprLbl::Not}])]
    Not(Box<Expr>),
    #[variant((Box<Expr[@s1]>, Box<Expr[@s2]>) -> Expr[s1 | s2 | #{ExprLbl::Or}])]
    Or(Box<Expr>, Box<Expr>),
    #[variant((Box<Expr[@s1]>, Box<Expr[@s2]>) -> Expr[s1 | s2 | #{ExprLbl::And}])]
    And(Box<Expr>, Box<Expr>),
    #[variant((Box<Expr[@s1]>, Box<Expr[@s2]>) -> Expr[s1 | s2 | #{ExprLbl::Xor}])]
    Xor(Box<Expr>, Box<Expr>),
}

impl Expr {
    #[spec(fn(&Expr[@s]) -> Box<Expr[s]>)]
    fn dup(&self) -> Box<Expr> {
        let e = match self {
            Expr::Var(x) => Expr::Var(*x),
            Expr::Cst(x) => Expr::Cst(*x),
            Expr::Not(x) => Expr::Not(x.dup()),
            Expr::Or(x, y) => Expr::Or(x.dup(), y.dup()),
            Expr::And(x, y) => Expr::And(x.dup(), y.dup()),
            Expr::Xor(x, y) => Expr::Xor(x.dup(), y.dup()),
        };
        Box::new(e)
    }

    #[spec(fn(&Expr{v: !set_is_in(ExprLbl::Var, v)}) -> bool)]
    fn eval(&self) -> bool {
        match self {
            Expr::Cst(x) => *x,
            Expr::Not(x) => !x.eval(),
            Expr::Or(x, y) => x.eval() || y.eval(),
            Expr::And(x, y) => x.eval() && y.eval(),
            Expr::Xor(x, y) => x.eval() != y.eval(),
            Expr::Var(_) => unreachable(),
        }
    }

    #[spec(
        fn(&Expr[@s])
        -> Expr { v: set_subset(v, (s - #{ExprLbl::Xor}) | #{ExprLbl::And, ExprLbl::Or, ExprLbl::Not}) }
    )]
    fn simplify(&self) -> Expr {
        match self {
            Expr::Var(x) => Expr::Var(*x),
            Expr::Cst(b) => Expr::Cst(*b),
            Expr::Not(x) => Expr::Not(Box::new(x.simplify())),
            Expr::Or(x, y) => Expr::Or(Box::new(x.simplify()), Box::new(y.simplify())),
            Expr::And(x, y) => Expr::And(Box::new(x.simplify()), Box::new(y.simplify())),
            Expr::Xor(x, y) => {
                let x1 = x.simplify();
                let y1 = y.simplify();
                Expr::Or(
                    Box::new(Expr::And(x1.dup(), Box::new(Expr::Not(y1.dup())))),
                    Box::new(Expr::And(Box::new(Expr::Not(Box::new(x1))), Box::new(y1))),
                )
            }
        }
    }

    #[spec( fn(&Expr[@s], _) -> Box<Expr{v: set_subset(v, (s - #{ExprLbl::Var}) | #{ExprLbl::Cst}) }> )]
    fn subst(&self, m: &HashMap<i32, bool>) -> Box<Expr> {
        let e = match self {
            Expr::Var(x) => Expr::Cst(m[x]),
            Expr::Cst(x) => Expr::Cst(*x),
            Expr::Not(x) => Expr::Not(x.subst(m)),
            Expr::Or(x, y) => Expr::Or(x.subst(m), y.subst(m)),
            Expr::And(x, y) => Expr::And(x.subst(m), y.subst(m)),
            Expr::Xor(x, y) => Expr::Xor(x.subst(m), y.subst(m)),
        };
        Box::new(e)
    }

    fn fastrun(&self, m: &HashMap<i32, bool>) -> bool {
        self.simplify().subst(m).fasteval()
    }

    #[spec(fn(&Expr{ s: set_subset(s, #{ExprLbl::Cst, ExprLbl::Not, ExprLbl::And, ExprLbl::Or}) }) -> bool)]
    fn fasteval(&self) -> bool {
        match self {
            Expr::Cst(x) => *x,
            Expr::Not(x) => !x.eval(),
            Expr::Or(x, y) => x.eval() || y.eval(),
            Expr::And(x, y) => x.eval() && y.eval(),
            Expr::Xor(..) | Expr::Var(_) => unreachable(),
        }
    }
}

#[spec(fn() -> _ requires false)]
fn unreachable() -> ! {
    loop {}
}
