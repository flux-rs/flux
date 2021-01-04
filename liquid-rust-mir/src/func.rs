use crate::{
    bblock::{BBlock, BBlockId},
    local::Local,
};

use liquid_rust_common::{
    index::{IndexMap},
    new_index,
};
use liquid_rust_ty::{BaseTy, FuncTy};

use std::fmt;

new_index! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    FuncId
}

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func{}", self.0)
    }
}

pub struct Func<S> {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMap<BBlockId, BBlock<S>>,
    ty: FuncTy,
    user_ty: bool,
}

impl<S> Func<S> {
    pub fn builder(arity: usize, bblocks_len: usize) -> FuncBuilder<S> {
        FuncBuilder {
            arity,
            local_decls: IndexMap::new(),
            bblocks: IndexMap::from_raw((0..bblocks_len).map(|_| None).collect()),
            ty: None,
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn return_ty(&self) -> &BaseTy {
        self.local_decls.get(Local::ret()).unwrap()
    }

    pub fn local_decls(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls.iter()
    }

    pub fn arguments(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls().skip(1).take(self.arity)
    }

    pub fn temporaries(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls().skip(self.arity + 1)
    }

    pub fn get_bblock(&self, bblock_id: BBlockId) -> &BBlock<S> {
        self.bblocks.get(bblock_id).unwrap()
    }

    pub fn bblocks(&self) -> impl Iterator<Item = (BBlockId, &BBlock<S>)> {
        self.bblocks.iter()
    }

    pub fn ty(&self) -> &FuncTy {
        &self.ty
    }

    pub fn user_ty(&self) -> bool {
        self.user_ty
    }
}

pub struct FuncBuilder<S> {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMap<BBlockId, Option<BBlock<S>>>,
    ty: Option<FuncTy>,
}

impl<S> FuncBuilder<S> {
    pub fn bblock_ids(&self) -> impl Iterator<Item = BBlockId> {
        self.bblocks.keys()
    }

    pub fn add_local_decl(&mut self, ty: BaseTy) -> Local {
        self.local_decls.insert(ty)
    }

    pub fn set_bblock(&mut self, bblock_id: BBlockId, bblock: BBlock<S>) -> bool {
        self.bblocks
            .get_mut(bblock_id)
            .unwrap()
            .replace(bblock)
            .is_some()
    }

    pub fn add_ty(&mut self, func_ty: FuncTy) {
        self.ty = Some(func_ty);
    }

    pub fn build(self) -> Result<Func<S>, BBlockId> {
        let mut bblocks = Vec::with_capacity(self.bblocks.len());

        for (bb_id, bb) in self.bblocks {
            bblocks.push(bb.ok_or(bb_id)?);
        }

        let (ty, user_ty) = if let Some(ty) = self.ty {
            (ty, true)
        } else {
            let arguments = self
                .local_decls
                .iter()
                .skip(1)
                .take(self.arity)
                .map(|(_, base_ty)| base_ty.refined())
                .collect::<Vec<_>>();

            let return_ty = self.local_decls.get(Local::ret()).unwrap().refined();

            (FuncTy::new(arguments, return_ty), false)
        };

        Ok(Func {
            arity: self.arity,
            local_decls: self.local_decls,
            bblocks: IndexMap::from_raw(bblocks),
            ty,
            user_ty,
        })
    }
}
