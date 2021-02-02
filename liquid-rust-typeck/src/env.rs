use crate::region_inference as region;
use ast::Proj;
use liquid_rust_core::{
    ast,
    names::{Local, Location},
    ty::{self, pred::Place, Heap, LocalsMap, Region, Ty, TyCtxt, TyS, Walk},
};
use std::{collections::HashSet, fmt};
use ty::{BorrowKind, TyKind};

use crate::constraint::Constraint;

pub struct Env<'a> {
    tcx: &'a TyCtxt,
    locals: Vec<LocalsMap>,
    heap: Heap,
}

impl<'a> Env<'a> {
    pub fn new(tcx: &'a TyCtxt) -> Self {
        Env {
            tcx,
            locals: vec![LocalsMap::empty()],
            heap: Heap::new(),
        }
    }
}

impl Env<'_> {
    pub fn alloc(&mut self, x: Local, ty: Ty) {
        let l = self.fresh_location();
        self.insert_local(x, l);
        self.heap.insert(l, ty);
    }

    pub fn update(&mut self, place: &ast::Place, ty: Ty) {
        let l = self.lookup_local(&place.base);
        let root = self.tcx.selfify(self.lookup_location(l), Place::from(*l));

        let fresh_l = self.fresh_location();
        let ty = self.update_ty(&root, &place.projs, ty);
        self.insert_local(place.base, fresh_l);
        self.heap.insert(fresh_l, ty);
    }

    pub fn borrow(&mut self, place: &ast::Place) -> Location {
        let ty = self.lookup(place).clone();
        let l = self.fresh_location();
        self.heap.insert(l, ty);
        l
    }

    pub fn drop(&mut self, place: &ast::Place) -> Constraint {
        let root = self.lookup(place).clone();
        let constraint = self.drop_ty(&root);
        self.update(place, self.tcx.uninitialize(&root));
        constraint
    }

    pub fn lookup(&self, place: &ast::Place) -> &Ty {
        let mut ty = self.lookup_location(self.lookup_local(&place.base));
        for proj in &place.projs {
            match (ty.kind(), proj) {
                (TyKind::Tuple(tuple), &Proj::Field(n)) => {
                    ty = tuple.ty_at(n);
                }
                (TyKind::Ref(.., l), Proj::Deref) => {
                    ty = self.lookup_location(l);
                }
                _ => bug!("{:?} {:?} {:?}", ty, place, proj),
            }
        }
        ty
    }

    pub fn check_ownership_safety(
        &self,
        kind: RefKind,
        place: &ast::Place,
        reborrow_list: &mut Vec<ast::Place>,
    ) -> Result<(), OwnershipError> {
        for (&x, l) in self.locals() {
            let ty = self.lookup_location(l);
            ty.walk(|ty, projs| {
                if let TyKind::Ref(bk, region, ..) = ty.kind() {
                    let in_reborrow_list = reborrow_list
                        .iter()
                        .any(|p| p.base == x && p.projs == projs);
                    if in_reborrow_list {
                        return Walk::Continue;
                    }
                    for p in region.places() {
                        if place.overlaps(p) && (kind >= RefKind::Mut || bk.is_mut()) {
                            let conflict = ast::Place::new(x, Vec::from(projs));
                            return Walk::Stop(OwnershipError::ConflictingBorrow(conflict));
                        }
                    }
                }
                Walk::Continue
            })?;
        }
        for (i, proj) in place.projs.iter().enumerate() {
            match proj {
                ast::Proj::Field(_) => {}
                ast::Proj::Deref => {
                    let prefix = ast::Place::new(place.base, Vec::from(&place.projs[0..i]));
                    let ty = self.lookup(&prefix);
                    reborrow_list.push(prefix);
                    match ty.kind() {
                        TyKind::Ref(bk, region, _) => {
                            if kind > *bk {
                                return Err(OwnershipError::BehindRef(*bk));
                            }
                            for p in region.places() {
                                let projs = p
                                    .projs
                                    .iter()
                                    .chain(&place.projs[i + 1..])
                                    .copied()
                                    .collect();
                                let place = &ast::Place::new(p.base, projs);
                                self.check_ownership_safety(kind, place, reborrow_list)?;
                            }
                        }
                        TyKind::OwnRef(_) => todo!(),
                        _ => {}
                    }
                    reborrow_list.pop();
                }
            }
        }
        Ok(())
    }

    pub fn resolve_place(&self, place: &ast::Place) -> Place {
        let mut base = *self.lookup_local(&place.base);
        let mut ty = self.lookup_location(&base);

        let mut projs = Vec::new();
        for proj in &place.projs {
            match (ty.kind(), proj) {
                (TyKind::Tuple(tup), &Proj::Field(n)) => {
                    ty = tup.ty_at(n);
                    projs.push(n);
                }
                (TyKind::Ref(.., l), Proj::Deref) => {
                    projs.clear();
                    base = *l;
                    ty = self.lookup_location(l);
                }
                _ => bug!(),
            }
        }

        Place {
            base: ty::Var::from(base),
            projs,
        }
    }

    pub fn extend_heap(&mut self, heap: &Heap) {
        for (l, ty) in heap {
            self.heap.insert(*l, ty.clone());
        }
    }

    pub fn insert_locals(&mut self, locals: LocalsMap) {
        self.locals.last_mut().unwrap().extend(locals);
    }

    pub fn heap(&self) -> &Heap {
        &self.heap
    }

    pub fn locals(&self) -> &LocalsMap {
        self.locals.last().unwrap()
    }

    pub fn vars_in_scope(&self) -> Vec<ty::Var> {
        self.heap.keys().map(|&l| ty::Var::Location(l)).collect()
    }

    pub fn snapshot(&mut self) -> Snapshot {
        let heap_len = self.heap.len();
        let locals_depth = self.locals.len();

        self.locals.push(self.locals.last().unwrap().clone());
        Snapshot {
            heap_len,
            locals_depth,
        }
    }

    pub fn snapshot_without_locals(&mut self) -> Snapshot {
        let heap_len = self.heap.len();
        let locals_depth = self.locals.len();

        self.locals.push(LocalsMap::empty());
        Snapshot {
            heap_len,
            locals_depth,
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    pub fn rollback_to(&mut self, snapshot: Snapshot) {
        self.heap.truncate(snapshot.heap_len);
        self.locals.truncate(snapshot.locals_depth);
    }

    pub fn capture_bindings<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, Vec<(Location, Ty)>) {
        let n = self.heap.len();
        let r = f(self);
        let bindings = self
            .heap
            .iter()
            .skip(n)
            .map(|(l, ty)| (*l, ty.clone()))
            .collect();
        (r, bindings)
    }

    // Private

    fn insert_local(&mut self, x: Local, l: Location) {
        self.locals.last_mut().unwrap().insert(x, l);
    }

    fn lookup_local(&self, x: &Local) -> &Location {
        self.locals
            .last()
            .unwrap()
            .get(x)
            .unwrap_or_else(|| panic!("Env: local not found {:?}", x))
    }

    fn lookup_location(&self, l: &Location) -> &Ty {
        self.heap
            .get(l)
            .unwrap_or_else(|| panic!("Env: location not found {:?}", l))
    }

    fn fresh_location(&self) -> Location {
        self.tcx.fresh::<Location>()
    }

    fn update_ty(&mut self, root: &TyS, projs: &[Proj], ty: Ty) -> Ty {
        match (root.kind(), projs) {
            (_, []) => ty,
            (ty::TyKind::Tuple(tup), [Proj::Field(n), ..]) => {
                let ty = self.update_ty(tup.ty_at(*n), &projs[1..], ty);
                self.tcx.mk_tuple(tup.map_ty_at(*n, |_| ty))
            }
            (ty::TyKind::Ref(bk, r, l), [Proj::Deref, ..]) => {
                let root = self.tcx.selfify(self.lookup_location(l), Place::from(*l));

                let fresh_l = self.fresh_location();
                let ty = self.update_ty(&root, &projs[1..], ty);
                self.heap.insert(fresh_l, ty);
                self.tcx.mk_ref(*bk, r.clone(), fresh_l)
            }
            (ty::TyKind::OwnRef(l), [Proj::Deref, ..]) => {
                let root = self.tcx.selfify(self.lookup_location(l), Place::from(*l));

                let fresh_l = self.fresh_location();
                let ty = self.update_ty(&root, &projs[1..], ty);
                self.heap.insert(fresh_l, ty);
                self.tcx.mk_own_ref(fresh_l)
            }
            _ => bug!("{} {:?}", root, projs),
        }
    }

    fn drop_ty(&mut self, ty: &Ty) -> Constraint {
        let vars_in_scope = self.vars_in_scope();
        let mut constraints = vec![];

        ty.walk(|ty, _| {
            if let TyKind::Ref(BorrowKind::Mut, r, l) = ty.kind() {
                let ty = self.lookup_location(l).clone();
                match r.places() {
                    [] => {}
                    [place] => {
                        self.update(place, ty);
                    }
                    places => {
                        // Get join
                        let ty_join = self.tcx.replace_with_fresh_vars(&ty, &vars_in_scope);
                        let mut region_constraints = region::Constraints::new();

                        constraints.push(shallow_subtyping(&ty, &ty_join, &mut region_constraints));
                        for place in r.places() {
                            let ty = self.lookup(place);
                            constraints.push(shallow_subtyping(
                                &ty,
                                &ty_join,
                                &mut region_constraints,
                            ));
                        }
                        let sol = region_constraints.solve();
                        let ty_join = sol.fix_regions_ty(self.tcx, &ty_join);

                        // Update places
                        for place in places {
                            self.update(place, ty_join.clone());
                        }
                    }
                }
            }
            Walk::Continue::<()>
        });
        Constraint::Conj(constraints)
    }

    pub fn outlives(region1: &Region, region2: &Region) -> bool {
        match (region1, region2) {
            (Region::Concrete(places1), Region::Concrete(places2)) => {
                let places1: HashSet<_> = places1.iter().collect();
                let places2: HashSet<_> = places2.iter().collect();
                places1.is_subset(&places2)
            }
            // TODO: we should consider outlive annotations here.
            (Region::Universal(_), _) | (_, Region::Universal(_)) => false,
            (Region::Infer(_), _) | (_, Region::Infer(_)) => bug!(),
        }
    }

    pub fn subtyping(&self, ty1: &Ty, heap2: &Heap, ty2: &Ty) -> Constraint {
        let tcx = self.tcx;
        let heap1 = &self.heap;
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Fn(..), TyKind::Fn(..)) => todo!(),
            (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => tup1
                .iter()
                .zip(tup2.types())
                .rev()
                .fold(Constraint::True, |c, ((f, ty1), ty2)| {
                    Constraint::Conj(vec![
                        self.subtyping(ty1, heap2, ty2),
                        Constraint::from_binding(*f, ty1.clone(), c),
                    ])
                }),
            // TODO check regions
            (TyKind::Ref(bk1, r1, l1), TyKind::Ref(bk2, r2, l2)) if bk1 >= bk2 => {
                assert!(Env::outlives(r1, r2));
                let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
                let ty2 = &heap2[l2];
                self.subtyping(ty1, heap2, ty2)
            }
            (TyKind::OwnRef(l1), TyKind::OwnRef(l2)) => {
                let ty1 = &tcx.selfify(&heap1[l1], Place::from(*l1));
                let ty2 = &heap2[l2];
                self.subtyping(ty1, heap2, ty2)
            }
            (TyKind::Refine(bty1, refine1), TyKind::Refine(bty2, refine2)) if bty1 == bty2 => {
                Constraint::from_subtype(*bty1, refine1, refine2)
            }
            (_, TyKind::Uninit(n)) if ty1.size() == *n => Constraint::True,
            _ => bug!("{} <: {}", ty1, ty2),
        }
    }
}

fn shallow_subtyping(
    ty1: &Ty,
    ty2: &Ty,
    region_constraints: &mut region::Constraints,
) -> Constraint {
    match (ty1.kind(), ty2.kind()) {
        (TyKind::Fn(_), TyKind::Fn(_)) => todo!(),
        (TyKind::Tuple(tup1), TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => tup1
            .iter()
            .zip(tup2.types())
            .rev()
            .fold(Constraint::True, |c, ((f, ty1), ty2)| {
                Constraint::Conj(vec![
                    shallow_subtyping(ty1, ty2, region_constraints),
                    Constraint::from_binding(*f, ty1.clone(), c),
                ])
            }),
        (TyKind::Refine(bty1, refine1), TyKind::Refine(bty2, refine2)) if bty1 == bty2 => {
            Constraint::from_subtype(*bty1, refine1, refine2)
        }
        (TyKind::Ref(bk1, r1, _), TyKind::Ref(bk2, r2, _)) if bk1 == bk2 => {
            region_constraints.add(r1.clone(), r2.clone());
            Constraint::True
        }
        (TyKind::Uninit(n1), TyKind::Uninit(n2)) if n1 == n2 => Constraint::True,
        (TyKind::OwnRef(_), TyKind::OwnRef(_)) => Constraint::True,
        _ => bug!("{} <: {}", ty1, ty2),
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum RefKind {
    Shared,
    Mut,
    Owned,
}

impl From<BorrowKind> for RefKind {
    fn from(bk: BorrowKind) -> Self {
        match bk {
            BorrowKind::Shared => RefKind::Shared,
            BorrowKind::Mut => RefKind::Mut,
        }
    }
}

impl std::cmp::PartialEq<BorrowKind> for RefKind {
    fn eq(&self, other: &BorrowKind) -> bool {
        matches!(
            (self, other),
            (RefKind::Shared, BorrowKind::Shared) | (RefKind::Mut, BorrowKind::Mut)
        )
    }
}

impl std::cmp::PartialOrd<BorrowKind> for RefKind {
    fn partial_cmp(&self, other: &BorrowKind) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        match (self, other) {
            (RefKind::Shared, BorrowKind::Shared) | (RefKind::Mut, BorrowKind::Mut) => Some(Equal),
            (RefKind::Mut, BorrowKind::Shared)
            | (RefKind::Owned, BorrowKind::Shared | BorrowKind::Mut) => Some(Greater),
            (RefKind::Shared, BorrowKind::Mut) => Some(Less),
        }
    }
}

#[derive(Debug)]
pub enum OwnershipError {
    ConflictingBorrow(ast::Place),
    BehindRef(BorrowKind),
}

pub struct Snapshot {
    heap_len: usize,
    locals_depth: usize,
}

impl fmt::Debug for Env<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.heap)?;
        let s = self
            .locals
            .last()
            .unwrap()
            .iter()
            .map(|(x, l)| format!("_{} => l{}", x.as_usize(), l.as_usize()))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", s)
    }
}
