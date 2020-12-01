use crate::{
    bblock::{BBlock, BBlockId},
    local::Local,
};

use liquid_rust_common::{
    def_index,
    index::{Index, IndexMap, IndexMapBuilder},
};
use liquid_rust_ty::{Argument, BaseTy, Ty};

use std::fmt;

def_index!(FuncId);

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "func{}", self.0)
    }
}

pub struct Func {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMap<BBlockId, BBlock>,
    ty: Ty,
    user_ty: bool,
}

impl Func {
    pub fn builder(arity: usize, bblocks_len: usize) -> FuncBuilder {
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

    pub fn get_bblock(&self, bblock_id: BBlockId) -> &BBlock {
        self.bblocks.get(bblock_id)
    }

    pub fn bblocks(&self) -> impl Iterator<Item = (BBlockId, &BBlock)> {
        self.bblocks.iter()
    }

    pub fn ty(&self) -> &Ty {
        &self.ty
    }

    pub fn user_ty(&self) -> bool {
        self.user_ty
    }
}

pub struct FuncBuilder {
    arity: usize,
    local_decls: IndexMap<Local, BaseTy>,
    bblocks: IndexMapBuilder<BBlockId, BBlock>,
    ty: Option<Ty>,
}

impl FuncBuilder {
    pub fn bblock_ids(&self) -> impl Iterator<Item = BBlockId> {
        self.bblocks.keys()
    }

    pub fn add_local_decl(&mut self, ty: BaseTy) -> Local {
        self.local_decls.insert(ty)
    }

    pub fn set_bblock(&mut self, bblock_id: BBlockId, bblock: BBlock) -> bool {
        self.bblocks.insert(bblock_id, bblock)
    }

    pub fn add_ty(&mut self, ty: Ty) {
        self.ty = Some(ty);
    }

    pub fn build(self) -> Result<Func, BBlockId> {
        let bblocks = self.bblocks.build()?;
        let (ty, user_ty) = if let Some(ty) = self.ty {
            (ty, true)
        } else {
            let arguments = self
                .local_decls
                .iter()
                .skip(1)
                .take(self.arity)
                .enumerate()
                .map(|(pos, (_, base_ty))| (Argument::new(pos, 0), base_ty.refined()))
                .collect::<Vec<_>>();

            let return_ty = self.local_decls.get(Local::first()).refined();

            (Ty::Func(arguments, Box::new(return_ty)), false)
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
