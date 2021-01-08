use ast::{Place, Proj};
use liquid_rust_core::{
    ast,
    names::{Local, Location},
    ty::{self, Heap, LocalsMap, Ty, TyCtxt},
};
use std::{collections::HashMap, fmt};
use ty::TyKind;

pub struct Env<'a> {
    locals: Vec<HashMap<Local, Location>>,
    heap: Heap,
    tcx: &'a TyCtxt,
}

impl<'a> Env<'a> {
    pub fn new(tcx: &'a TyCtxt) -> Self {
        Env {
            locals: vec![HashMap::new()],
            heap: Heap::new(),
            tcx,
        }
    }
}

impl Env<'_> {
    pub fn insert_heap(&mut self, heap: &Heap) {
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

    pub fn snapshot(&mut self) -> Snapshot {
        let heap_len = self.heap.len();
        let locals_len = self.locals.len();

        self.locals.push(self.locals.last().unwrap().clone());
        Snapshot {
            heap_len,
            locals_len,
        }
    }

    pub fn snapshot_without_locals(&mut self) -> Snapshot {
        let heap_len = self.heap.len();
        let locals_len = self.locals.len();

        self.locals.push(HashMap::new());
        Snapshot {
            heap_len,
            locals_len,
        }
    }

    pub fn rollback_to(&mut self, snapshot: Snapshot) -> Heap {
        self.locals.truncate(snapshot.locals_len);
        self.heap.split_off(snapshot.heap_len)
    }

    pub fn alloc(&mut self, x: Local, ty: Ty) {
        let l = self.fresh_location();
        self.insert_local(x, l);
        self.heap.insert(l, ty);
    }

    pub fn update(&mut self, place: &Place, ty: Ty) {
        let root = self.lookup(&Place::from(place.base)).clone();
        let ty = self.update_ty(&root, &place.projs, ty);
        let l = self.fresh_location();
        self.insert_local(place.base, l);
        self.heap.insert(l, ty);
    }

    pub fn borrow(&mut self, place: &Place) -> Location {
        let ty = self.lookup(place).clone();
        let l = self.fresh_location();
        self.heap.insert(l, ty);
        l
    }

    // TODO self-ification
    fn update_ty(&mut self, root: &Ty, projs: &[Proj], ty: Ty) -> Ty {
        match (root.kind(), projs) {
            (_, []) => ty,
            (ty::TyKind::Tuple(tup), [ast::Proj::Field(n), ..]) => {
                let new_ty = self.update_ty(tup.ty_at(*n), &projs[1..], ty);
                let tup = tup.map_ty_at(*n, |_| new_ty);
                self.tcx.mk_tuple(tup)
            }
            (ty::TyKind::Ref(bk, r, l), [ast::Proj::Deref, ..]) => {
                let fresh_l = self.fresh_location();
                let new_ty = self.update_ty(&self.get_ty(l).clone(), &projs[1..], ty);
                self.heap.insert(fresh_l, new_ty);
                self.tcx.mk_ref(*bk, r.clone(), fresh_l)
            }
            (ty::TyKind::OwnRef(_l), [ast::Proj::Deref, ..]) => todo!(),
            _ => bug!(),
        }
    }

    pub fn drop(&mut self, x: &Local) {
        let place = Place::from(*x);
        let size = self.lookup(&place).size();
        self.update(&place, self.tcx.mk_uninit(size))
    }

    pub fn lookup(&self, place: &Place) -> &Ty {
        let mut ty = self.get_ty(self.get_location(&place.base));
        for p in &place.projs {
            match (ty.kind(), p) {
                (TyKind::Tuple(tuple), &Proj::Field(n)) => {
                    ty = tuple.ty_at(n);
                }
                (TyKind::Ref(.., l), Proj::Deref) => {
                    ty = self.get_ty(l);
                }
                _ => bug!("{:?} {:?} {:?}", ty, place, p),
            }
        }
        ty
    }

    fn insert_local(&mut self, x: Local, l: Location) {
        self.locals.last_mut().unwrap().insert(x, l);
    }

    fn get_location(&self, x: &Local) -> &Location {
        self.locals.last().unwrap().get(x).unwrap()
    }

    fn get_ty(&self, l: &Location) -> &Ty {
        self.heap
            .get(l)
            .expect(&format!("Env: location not found {:?}", l))
    }

    fn fresh_location(&self) -> Location {
        self.tcx.fresh_location()
    }
}

pub struct Snapshot {
    heap_len: usize,
    locals_len: usize,
}

impl fmt::Debug for Env<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n", self.heap)?;
        let s = self
            .locals
            .last()
            .unwrap()
            .iter()
            .map(|(x, l)| format!("$x{} => $l{}", x.0, l.0))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", s)
    }
}
