use std::fmt;

use super::{ast::*, subst::ApplySubst, subst::DeferredSubst, subst::Subst};

#[derive(Debug)]
pub enum Constraint {
    Pred(PredC),
    Conj(Vec<Constraint>),
    Forall {
        bind: Symbol,
        ty: BasicType,
        hyp: PredC,
        body: Box<Constraint>,
    },
    Guard(PredC, Box<Constraint>),
    True,
    Err,
}

pub enum PredC {
    Var(Symbol),
    Constant(Constant),
    BinaryOp(BinOp, Box<PredC>, Box<PredC>),
    UnaryOp(UnOp, Box<PredC>),
    Iff(Box<PredC>, Box<PredC>),
    Kvar(u32, Vec<Symbol>),
}

impl Constraint {
    pub fn from_bindings<'a, I, V, T>(bindings: I, mut body: Constraint) -> Self
    where
        I: DoubleEndedIterator<Item = (V, T)>,
        V: Into<Var>,
        T: Into<DeferredSubst<Ty<'a>>>,
    {
        for (x, typ) in bindings.rev() {
            for (y, ty, hyp) in embed(x.into(), typ.into()).into_iter().rev() {
                body = Constraint::Forall {
                    bind: y,
                    ty,
                    hyp,
                    body: box body,
                }
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
            bind: Symbol::intern(&format!("{:?}", Var::Nu)),
            ty,
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
                let (y, inner) = subst.get(*x).unwrap_or((*x, vec![]));
                PredC::Var(place_to_symbol(y, inner.iter().chain(outter)))
            }
            PredS::BinaryOp(op, lhs, rhs) => {
                PredC::BinaryOp(*op, box lhs.apply(subst), box rhs.apply(subst))
            }
            PredS::UnaryOp(op, p) => PredC::UnaryOp(*op, box p.apply(subst)),
            PredS::Iff(lhs, rhs) => PredC::Iff(box lhs.apply(subst), box rhs.apply(subst)),
            PredS::Kvar(n, vars) => {
                let vars = vars.iter().map(|v| v.apply(subst)).collect();
                PredC::Kvar(*n, vars)
            }
        }
    }
}

impl ApplySubst<Symbol> for Var {
    fn apply(&self, subst: &Subst) -> Symbol {
        let (x, proj) = subst.get(*self).unwrap_or((*self, vec![]));
        place_to_symbol(x, &proj)
    }
}

impl<'a> From<Pred<'a>> for PredC {
    fn from(pred: Pred<'a>) -> Self {
        pred.apply(&Subst::empty())
    }
}

fn embed(x: Var, typ: DeferredSubst<Ty>) -> Vec<(Symbol, BasicType, PredC)> {
    let (subst, typ) = typ.split();
    let mut v = Vec::new();
    collect_field_map(x, &vec![], typ, &mut v);
    let subst = subst.extend(v);
    embed_(x, &mut vec![], typ, &subst)
}

fn collect_field_map(x: Var, proj: &Vec<u32>, typ: Ty, v: &mut Vec<(Var, (Var, Vec<u32>))>) {
    match typ {
        TyS::Tuple(fields) => {
            for (i, (f, t)) in fields.iter().enumerate() {
                let mut clone = proj.clone();
                clone.push(i as u32);
                collect_field_map(x, &clone, t, v);
                v.push(((*f).into(), (x, clone)));
            }
        }
        _ => {}
    }
}

fn embed_(x: Var, proj: &mut Vec<u32>, typ: Ty, subst: &Subst) -> Vec<(Symbol, BasicType, PredC)> {
    match typ {
        TyS::Refine { pred, ty } => {
            let subst = subst.extend(vec![(Var::Nu, (x, proj.clone()))]);
            vec![(place_to_symbol(x, proj.iter()), *ty, pred.apply(&subst))]
        }
        TyS::Tuple(fields) => {
            let mut v = vec![];
            for i in 0..fields.len() {
                proj.push(i as u32);
                v.extend(embed_(x, proj, fields[i].1, subst));
                proj.pop();
            }
            v
        }
        TyS::Fn { .. } | TyS::OwnRef(_) | TyS::Uninit(_) => vec![],
        TyS::RefineHole { .. } => bug!(""),
    }
}

fn place_to_symbol<'a, I>(var: Var, projection: I) -> Symbol
where
    I: IntoIterator<Item = &'a u32>,
{
    let mut s = format!("{:?}", var);
    for p in projection {
        s.push_str(&format!(".{}", p));
    }
    Symbol::intern(&s)
}

impl fmt::Debug for PredC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredC::Constant(c) => write!(f, "{:?}", c)?,
            PredC::Var(s) => {
                write!(f, "{}", &*s.as_str())?;
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
            PredC::Kvar(_, _) => todo!(),
        }
        Ok(())
    }
}
