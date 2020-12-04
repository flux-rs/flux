use crate::{
    bblock::{BBlock, BBlockId},
    local::Local,
};

use liquid_rust_common::{
    def_index,
    index::{Index, IndexMap, IndexMapBuilder},
};
use liquid_rust_ty::{BaseTy, FuncTy};

use std::fmt;

def_index!(FuncId);

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
            local_decls: Local::index_map(),
            bblocks: BBlockId::index_map_builder(bblocks_len),
            ty: None,
        }
    }

    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn return_ty(&self) -> &BaseTy {
        self.local_decls.get(Local::first())
    }

    pub fn arguments(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls.iter().skip(1).take(self.arity)
    }

    pub fn temporaries(&self) -> impl Iterator<Item = (Local, &BaseTy)> {
        self.local_decls.iter().skip(self.arity + 1)
    }

    pub fn get_bblock(&self, bblock_id: BBlockId) -> &BBlock<S> {
        self.bblocks.get(bblock_id)
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
    bblocks: IndexMapBuilder<BBlockId, BBlock<S>>,
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
        self.bblocks.insert(bblock_id, bblock)
    }

    pub fn add_ty(&mut self, func_ty: FuncTy) {
        self.ty = Some(func_ty);
    }

    pub fn build(self) -> Result<Func<S>, BBlockId> {
        let bblocks = self.bblocks.build()?;
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

            let return_ty = self.local_decls.get(Local::first()).refined();

            (FuncTy::new(arguments, return_ty), false)
        };
        Ok(Func {
            arity: self.arity,
            local_decls: self.local_decls,
            bblocks,
            ty,
            user_ty,
        })
    }
}
