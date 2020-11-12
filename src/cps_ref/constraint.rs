use std::fmt;

use super::{ast::*, subst::ApplySubst, subst::DeferredSubst, subst::Subst};

#[derive(Debug)]
pub enum Constraint {
    Pred(PredC),
    Conj(Vec<Constraint>),
    Forall {
        bind: Var,
        sort: Sort,
        hyp: PredC,
        body: Box<Constraint>,
    },
    Guard(PredC, Box<Constraint>),
    True,
    Err,
}

#[derive(Debug)]
pub enum Sort {
    Int,
    Bool,
    Tuple(Vec<Sort>),
}

impl From<BasicType> for Sort {
    fn from(ty: BasicType) -> Self {
        match ty {
            BasicType::Bool => Sort::Bool,
            BasicType::Int => Sort::Int,
        }
    }
}

pub type Kvar = (u32, Vec<Sort>);

impl From<Ty<'_>> for Sort {
    fn from(typ: Ty<'_>) -> Self {
        match typ {
            TyS::Tuple(fields) => Sort::Tuple(fields.iter().map(|&(_, t)| Sort::from(t)).collect()),
            &TyS::Refine { ty, .. } => Sort::from(ty),
            TyS::Fn { .. } | TyS::OwnRef(_) | TyS::Uninit(_) | TyS::Ref(..) => Self::Int,
            TyS::RefineHole { .. } => bug!(),
        }
    }
}
pub struct Place {
    pub var: Var,
    pub proj: Vec<u32>,
}

pub enum PredC {
    Place(Place),
    Constant(ConstantP),
    BinaryOp(BinOp, Box<PredC>, Box<PredC>),
    Conj(Vec<PredC>),
    UnaryOp(UnOp, Box<PredC>),
    Iff(Box<PredC>, Box<PredC>),
    Kvar(u32, Vec<Place>),
}

impl Constraint {
    pub fn from_bindings<'a, I, V, T>(bindings: I, mut body: Constraint) -> Self
    where
        I: DoubleEndedIterator<Item = (V, T)>,
        V: Into<Var>,
        T: Into<DeferredSubst<Ty<'a>>>,
    {
        for (x, typ) in bindings.rev() {
            let bind = x.into();
            let (sort, hyp) = embed(bind, typ.into());
            body = Constraint::Forall {
                bind,
                sort,
                hyp,
                body: box body,
            }
        }
        body
    }

    pub fn from_binding<'a, V, T>(bind: V, typ: T, body: Constraint) -> Self
    where
        V: Into<Var>,
        T: Into<DeferredSubst<Ty<'a>>>,
    {
        Self::from_bindings(vec![(bind, typ)].into_iter(), body)
    }

    pub fn from_subtype<'a>(
        ty: BasicType,
        pred1: DeferredSubst<Pred<'a>>,
        pred2: DeferredSubst<Pred<'a>>,
    ) -> Self {
        Constraint::Forall {
            bind: Var::Nu,
            sort: Sort::from(ty),
            hyp: pred1.apply(),
            body: box Constraint::Pred(pred2.apply()),
        }
    }

    pub fn guard<'a>(pred: impl Into<DeferredSubst<Pred<'a>>>, body: Constraint) -> Self {
        let p: DeferredSubst<Pred> = pred.into();
        Constraint::Guard(p.apply(), box body)
    }
}

impl<'a> ApplySubst<PredC> for Pred<'a> {
    fn apply(&self, subst: &Subst) -> PredC {
        match self {
            PredS::Constant(c) => PredC::Constant(*c),
            PredS::Place {
                var: x,
                projection: outter,
            } => {
                let (var, mut proj) = subst.get(*x).unwrap_or((*x, vec![]));
                proj.extend(outter);
                PredC::Place(Place { var, proj })
            }
            PredS::BinaryOp(op, lhs, rhs) => {
                PredC::BinaryOp(*op, box lhs.apply(subst), box rhs.apply(subst))
            }
            PredS::UnaryOp(op, p) => PredC::UnaryOp(*op, box p.apply(subst)),
            PredS::Iff(lhs, rhs) => PredC::Iff(box lhs.apply(subst), box rhs.apply(subst)),
            PredS::Kvar(n, vars) => PredC::Kvar(*n, vars.iter().map(|v| v.apply(subst)).collect()),
        }
    }
}

impl<'a> ApplySubst<Place> for Var {
    fn apply(&self, subst: &Subst) -> Place {
        let (var, proj) = subst.get(*self).unwrap_or((*self, vec![]));
        Place { var, proj }
    }
}

impl<'a> From<Pred<'a>> for PredC {
    fn from(pred: Pred<'a>) -> Self {
        pred.apply(&Subst::empty())
    }
}

fn embed(x: Var, typ: DeferredSubst<Ty>) -> (Sort, PredC) {
    let (subst, typ) = typ.split();
    let subst = subst.extend(collect_field_map(x, typ));
    (Sort::from(typ), embed_rec(x, typ, &subst, &mut vec![]))
}

fn embed_rec(x: Var, typ: Ty, subst: &Subst, proj: &mut Vec<u32>) -> PredC {
    match typ {
        &TyS::Refine { pred, .. } => {
            let subst = subst.extend(vec![(Var::Nu, (x, proj.clone()))]);
            pred.apply(&subst)
        }
        TyS::Tuple(fields) => {
            let preds = fields
                .iter()
                .enumerate()
                .map(|(i, (_, t))| {
                    proj.push(i as u32);
                    let pred = embed_rec(x, t, subst, proj);
                    proj.pop();
                    pred
                })
                .collect();
            PredC::Conj(preds)
        }
        TyS::Fn { .. } | TyS::OwnRef(_) | TyS::Uninit(_) | TyS::Ref(..) => {
            PredC::Constant(ConstantP::Bool(true))
        }
        TyS::RefineHole { .. } => bug!(),
    }
}

fn collect_field_map(x: Var, typ: Ty) -> Vec<(Var, (Var, Vec<u32>))> {
    let mut v = vec![];
    typ.walk(|path, typ| match typ {
        TyS::Tuple(fields) => {
            for (i, &(f, _)) in fields.iter().enumerate() {
                let mut clone = path.clone();
                clone.push(i as u32);
                v.push((Var::from(f), (x, clone)));
            }
        }
        _ => {}
    });
    v
}

impl fmt::Debug for PredC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredC::Constant(c) => write!(f, "{:?}", c)?,
            PredC::Place(Place { var, proj }) => {
                write!(f, "{:?}", var)?;
                for p in proj {
                    write!(f, ".{}", p)?
                }
            }
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(f, "({:?} {:?} {:?})", lhs, op, rhs)?;
            }
            PredC::UnaryOp(op, operand) => {
                write!(f, "{:?}({:?})", op, operand)?;
            }
            PredC::Iff(lhs, rhs) => {
                write!(f, "({:?} <=> {:?})", lhs, rhs)?;
            }
            PredC::Kvar(n, vars) => {
                write!(f, "$k{}{:?}", n, vars)?;
            }
            PredC::Conj(preds) => {
                let joined = preds
                    .iter()
                    .map(|p| format!("({:?})", p))
                    .collect::<Vec<_>>()
                    .join(" and ");
                write!(f, "{}", joined)?;
            }
        }
        Ok(())
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.var)?;
        for p in &self.proj {
            write!(f, ".{}", p)?
        }
        Ok(())
    }
}
