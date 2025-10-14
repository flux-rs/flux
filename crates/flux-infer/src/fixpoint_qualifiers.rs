use std::sync::LazyLock;

use liquid_fixpoint::{BinOp, BinRel, Sort};

use crate::fixpoint_encoding::fixpoint::{
    LocalVar, Var,
    fixpoint_generated::{Expr, Qualifier},
};
pub(crate) static FIXPOINT_QUALIFIERS: LazyLock<[Qualifier; 13]> = LazyLock::new(|| {
    // UNARY
    let eqtrue = Qualifier {
        name: String::from("EqTrue"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Bool)],
        body: Expr::Var(Var::Local(LocalVar::from(0u32))),
    };
    let eqfalse = Qualifier {
        name: String::from("EqFalse"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Bool)],
        body: Expr::Not(Box::new(Expr::Var(Var::Local(LocalVar::from(0u32))))),
    };
    let eqzero = Qualifier {
        name: String::from("EqZero"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Int)],
        body: Expr::Atom(
            BinRel::Eq,
            Box::new([Expr::Var(Var::Local(LocalVar::from(0u32))), Expr::int(0)]),
        ),
    };
    let gtzero = Qualifier {
        name: String::from("GtZero"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Int)],
        body: Expr::Atom(
            BinRel::Gt,
            Box::new([Expr::Var(Var::Local(LocalVar::from(0u32))), Expr::int(0)]),
        ),
    };
    let gezero = Qualifier {
        name: String::from("GeZero"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Int)],
        body: Expr::Atom(
            BinRel::Ge,
            Box::new([Expr::Var(Var::Local(LocalVar::from(0u32))), Expr::int(0)]),
        ),
    };
    let ltzero = Qualifier {
        name: String::from("LtZero"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Int)],
        body: Expr::Atom(
            BinRel::Lt,
            Box::new([Expr::Var(Var::Local(LocalVar::from(0u32))), Expr::int(0)]),
        ),
    };
    let lezero = Qualifier {
        name: String::from("LeZero"),
        args: vec![(Var::Local(LocalVar::from(0u32)), Sort::Int)],
        body: Expr::Atom(
            BinRel::Le,
            Box::new([Expr::Var(Var::Local(LocalVar::from(0u32))), Expr::int(0)]),
        ),
    };

    // BINARY
    let eq = Qualifier {
        name: String::from("Eq"),
        args: vec![
            (Var::Local(LocalVar::from(0u32)), Sort::Int),
            (Var::Local(LocalVar::from(1u32)), Sort::Int),
        ],
        body: Expr::Atom(
            BinRel::Eq,
            Box::new([
                Expr::Var(Var::Local(LocalVar::from(0u32))),
                Expr::Var(Var::Local(LocalVar::from(1u32))),
            ]),
        ),
    };
    let gt = Qualifier {
        name: String::from("Gt"),
        args: vec![
            (Var::Local(LocalVar::from(0u32)), Sort::Int),
            (Var::Local(LocalVar::from(1u32)), Sort::Int),
        ],
        body: Expr::Atom(
            BinRel::Gt,
            Box::new([
                Expr::Var(Var::Local(LocalVar::from(0u32))),
                Expr::Var(Var::Local(LocalVar::from(1u32))),
            ]),
        ),
    };
    let ge: liquid_fixpoint::Qualifier<crate::fixpoint_encoding::fixpoint::FixpointTypes> =
        Qualifier {
            name: String::from("Ge"),
            args: vec![
                (Var::Local(LocalVar::from(0u32)), Sort::Int),
                (Var::Local(LocalVar::from(1u32)), Sort::Int),
            ],
            body: Expr::Atom(
                BinRel::Ge,
                Box::new([
                    Expr::Var(Var::Local(LocalVar::from(0u32))),
                    Expr::Var(Var::Local(LocalVar::from(1u32))),
                ]),
            ),
        };
    let lt = Qualifier {
        name: String::from("Lt"),
        args: vec![
            (Var::Local(LocalVar::from(0u32)), Sort::Int),
            (Var::Local(LocalVar::from(1u32)), Sort::Int),
        ],
        body: Expr::Atom(
            BinRel::Lt,
            Box::new([
                Expr::Var(Var::Local(LocalVar::from(0u32))),
                Expr::Var(Var::Local(LocalVar::from(1u32))),
            ]),
        ),
    };
    let le = Qualifier {
        name: String::from("Le"),
        args: vec![
            (Var::Local(LocalVar::from(0u32)), Sort::Int),
            (Var::Local(LocalVar::from(1u32)), Sort::Int),
        ],
        body: Expr::Atom(
            BinRel::Le,
            Box::new([
                Expr::Var(Var::Local(LocalVar::from(0u32))),
                Expr::Var(Var::Local(LocalVar::from(1u32))),
            ]),
        ),
    };
    let le1 = Qualifier {
        name: String::from("Le1"),
        args: vec![
            (Var::Local(LocalVar::from(0u32)), Sort::Int),
            (Var::Local(LocalVar::from(1u32)), Sort::Int),
        ],
        body: Expr::Atom(
            BinRel::Le,
            Box::new([
                Expr::Var(Var::Local(LocalVar::from(0u32))),
                Expr::BinaryOp(
                    BinOp::Sub,
                    Box::new([Expr::Var(Var::Local(LocalVar::from(1u32))), Expr::int(1)]),
                ),
            ]),
        ),
    };
    [eqtrue, eqfalse, eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
});
