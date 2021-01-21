use std::{collections::HashMap, fmt};

use liquid_rust_core::{
    names::Field,
    ty::{
        self,
        pred::{Constant, Place},
        BaseTy, BinOp, KVid, Ty, TyS, UnOp,
    },
};

use liquid_rust_liquid as liquid;
use ty::{PredKind, TyKind, Var};

#[derive(Debug)]
pub enum Constraint {
    True,
    Pred(Pred),
    Conj(Vec<Constraint>),
    Forall(Var, Sort, Pred, Box<Constraint>),
    Guard(Pred, Box<Constraint>),
}

impl Constraint {
    pub fn from_binding<T: Into<Var>>(x: T, ty: Ty, body: Constraint) -> Constraint {
        Constraint::from_bindings(vec![(x, ty)], body)
    }

    pub fn from_bindings<T: Into<Var>>(bindings: Vec<(T, Ty)>, body: Constraint) -> Constraint {
        bindings.into_iter().rev().fold(body, |c, (x, ty)| {
            let var = x.into();
            let pred = embed_ty(var, &ty);
            Constraint::Forall(var, Sort::from(&ty), pred, box c)
        })
    }

    pub fn from_subtype(bty: ty::BaseTy, refine1: &ty::Refine, refine2: &ty::Refine) -> Constraint {
        Constraint::Forall(
            Var::Nu,
            Sort::from(bty),
            embed_refine(refine1, &Place::from(Var::Nu), &HashMap::new()),
            box Constraint::Pred(embed_refine(
                refine2,
                &Place::from(Var::Nu),
                &HashMap::new(),
            )),
        )
    }

    pub fn guard(pred: &ty::Pred, body: Constraint) -> Constraint {
        Constraint::Guard(
            Pred::Expr(embed_pred(pred, &Place::from(Var::Nu), &HashMap::new())),
            box body,
        )
    }
}

#[derive(Debug)]
pub enum Sort {
    Int,
    Bool,
    Unit,
    Tuple(Vec<Sort>),
}

impl<'a> From<&'a Ty> for Sort {
    fn from(ty: &'a Ty) -> Self {
        match ty.kind() {
            TyKind::Tuple(tup) => Sort::Tuple(tup.types().map(Sort::from).collect()),
            TyKind::Refine(bty, _) => Sort::from(*bty),
            TyKind::Fn(_) | TyKind::OwnRef(_) | TyKind::Ref(_, _, _) | TyKind::Uninit(_) => {
                Sort::Int
            }
        }
    }
}

impl From<BaseTy> for Sort {
    fn from(bty: BaseTy) -> Self {
        match bty {
            BaseTy::Int | BaseTy::Unit => Sort::Int,
            BaseTy::Bool => Sort::Bool,
        }
    }
}

#[derive(Debug)]
pub enum Pred {
    Kvar(Kvar),
    Conj(Vec<Pred>),
    Expr(Expr),
    True,
}

#[derive(Debug)]
pub enum Expr {
    Place(Place),
    Constant(Constant),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    UnaryOp(UnOp, Box<Expr>),
}

pub struct Kvar(KVid, Vec<Place>);

impl fmt::Display for Kvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = (self.1)
            .iter()
            .map(|v| format!("{}", v))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "$k{}[{}]", (self.0).0, vars)
    }
}

impl fmt::Debug for Kvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

fn collect_field_map(place: &mut Place, ty: &TyS, map: &mut HashMap<Field, Place>) {
    if let TyKind::Tuple(tup) = ty.kind() {
        for (i, (fld, ty)) in tup.iter().enumerate() {
            place.projs.push(i);
            map.insert(*fld, place.clone());
            collect_field_map(place, ty, map);
            place.projs.pop();
        }
    }
}

fn embed_ty(var: Var, ty: &TyS) -> Pred {
    let mut fld_map = HashMap::new();
    let mut place = Place::from(var);
    collect_field_map(&mut place, ty, &mut fld_map);
    embed_ty_rec(ty, &place, &fld_map)
}

fn embed_ty_rec(ty: &TyS, nu: &Place, fld_map: &HashMap<Field, Place>) -> Pred {
    match ty.kind() {
        TyKind::Tuple(tup) => {
            let preds = tup
                .types()
                .enumerate()
                .map(|(i, ty)| embed_ty_rec(ty, &nu.extend_path(i), fld_map))
                .collect();
            Pred::Conj(preds)
        }
        TyKind::Refine(_, refine) => embed_refine(refine, &nu, fld_map),
        TyKind::OwnRef(_) | TyKind::Ref(..) | TyKind::Fn(..) | TyKind::Uninit(..) => Pred::True,
    }
}

fn embed_refine(refine: &ty::Refine, nu: &Place, fld_map: &HashMap<Field, Place>) -> Pred {
    match refine {
        ty::Refine::Pred(pred) => Pred::Expr(embed_pred(pred, nu, fld_map)),
        ty::Refine::Infer(kvar) => Pred::Kvar(embed_kvar(kvar, nu, fld_map)),
    }
}

fn embed_pred(pred: &ty::Pred, nu: &Place, fld_map: &HashMap<Field, Place>) -> Expr {
    match pred.kind() {
        PredKind::Constant(c) => Expr::Constant(*c),
        PredKind::BinaryOp(bin_op, op1, op2) => Expr::BinaryOp(
            *bin_op,
            box embed_pred(op1, nu, fld_map),
            box embed_pred(op2, nu, fld_map),
        ),
        PredKind::UnaryOp(un_op, op) => Expr::UnaryOp(*un_op, box embed_pred(op, nu, fld_map)),
        PredKind::Place(place) => Expr::Place(embed_place(place, nu.clone(), fld_map)),
    }
}

fn embed_place(place: &Place, nu: Place, fld_map: &HashMap<Field, Place>) -> Place {
    let mut new_place = match place.base {
        Var::Nu => nu,
        Var::Location(l) => Place::from(l),
        Var::Field(fld) => fld_map
            .get(&fld)
            .cloned()
            .unwrap_or_else(|| Place::from(fld)),
    };
    new_place.projs.extend(&place.projs);
    new_place
}

fn embed_kvar(kvar: &ty::Kvar, nu: &Place, fld_map: &HashMap<Field, Place>) -> Kvar {
    let mut places = vec![];
    for var in &kvar.1 {
        match var {
            Var::Field(fld) => places.push(
                fld_map
                    .get(fld)
                    .cloned()
                    .unwrap_or_else(|| Place::from(*fld)),
            ),
            Var::Location(l) => places.push(Place::from(*l)),
            Var::Nu => places.push(nu.clone()),
        }
    }
    Kvar(kvar.0, places)
}

// Lowering

impl Sort {
    fn flatten(&self) -> Vec<(liquid::Sort, Vec<usize>)> {
        let mut vec = vec![];
        self.flatten_rec(&mut vec![], &mut vec);
        vec
    }

    fn flatten_rec(&self, path: &mut Vec<usize>, vec: &mut Vec<(liquid::Sort, Vec<usize>)>) {
        match self {
            Sort::Int => vec.push((liquid::Sort::Int, path.clone())),
            Sort::Bool => vec.push((liquid::Sort::Bool, path.clone())),
            Sort::Unit => vec.push((liquid::Sort::Unit, path.clone())),
            Sort::Tuple(sorts) => {
                for (i, sort) in sorts.iter().enumerate() {
                    path.push(i);
                    sort.flatten_rec(path, vec);
                    path.pop();
                }
            }
        }
    }
}

impl Constraint {
    pub fn lower(self) -> liquid::Constraint {
        self.lower_(&mut HashMap::new())
    }

    fn lower_(self, sorts: &mut HashMap<Var, Sort>) -> liquid::Constraint {
        match self {
            Constraint::True => liquid::Constraint::True,
            Constraint::Pred(pred) => liquid::Constraint::Pred(pred.lower(sorts)),
            Constraint::Conj(constraints) => {
                liquid::Constraint::Conj(constraints.into_iter().map(|c| c.lower_(sorts)).collect())
            }
            Constraint::Forall(var, sort, pred, body) => {
                let pred = pred.lower(sorts);
                // The sort need to be added to the scope after lowering the predicate, because
                // field variables in the predicate have already been expanded during embedding
                sorts.insert(var, sort);
                let body = body.lower_(sorts);
                let mut iter = sorts.remove(&var).unwrap().flatten().into_iter().rev();
                if let Some((sort, projs)) = iter.next() {
                    let body = liquid::Constraint::Forall(
                        place_to_string(var, projs),
                        sort,
                        pred,
                        box body,
                    );
                    iter.fold(body, |body, (sort, projs)| {
                        liquid::Constraint::Forall(
                            place_to_string(var, projs),
                            sort,
                            liquid::Pred::True,
                            box body,
                        )
                    })
                } else {
                    liquid::Constraint::True
                }
            }
            Constraint::Guard(guard, body) => {
                liquid::Constraint::Guard(guard.lower(sorts), box body.lower_(sorts))
            }
        }
    }
}

impl Pred {
    pub fn lower(self, vars: &HashMap<Var, Sort>) -> liquid::Pred {
        match self {
            Pred::Kvar(kvar) => liquid::Pred::Kvar(kvar.lower(vars)),
            Pred::Conj(preds) => {
                liquid::Pred::Conj(preds.into_iter().map(|p| p.lower(vars)).collect())
            }
            Pred::Expr(expr) => liquid::Pred::Expr(expr.lower(vars)),
            Pred::True => liquid::Pred::True,
        }
    }
}

impl Expr {
    pub fn lower(self, vars: &HashMap<Var, Sort>) -> liquid::Expr {
        match self {
            Expr::Place(place) => liquid::Expr::Var(place_to_string(place.base, place.projs)),
            Expr::Constant(c) => liquid::Expr::Constant(c),
            Expr::BinaryOp(bin_op, op1, op2) => {
                liquid::Expr::BinaryOp(bin_op, box op1.lower(vars), box op2.lower(vars))
            }
            Expr::UnaryOp(un_op, op) => liquid::Expr::UnaryOp(un_op, box op.lower(vars)),
        }
    }
}

impl Kvar {
    pub fn lower(self, sorts: &HashMap<Var, Sort>) -> liquid::Kvar {
        let mut vars = vec![];
        for place in self.1 {
            match sorts.get(&place.base) {
                Some(sort) => {
                    for (_, mut projs) in sort.flatten() {
                        projs.extend(place.projs.iter());
                        vars.push(place_to_string(place.base, projs));
                    }
                }
                None => {
                    vars.push(place_to_string(place.base, place.projs));
                }
            }
        }
        liquid::Kvar((self.0).0, vars)
    }
}

fn place_to_string(base: Var, projs: Vec<usize>) -> String {
    let mut s = format!("{}", base);
    for p in projs {
        s.push_str(&format!(".{}", p));
    }
    s
}
