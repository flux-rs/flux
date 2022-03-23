use crate::ty::{self, Name, ParamTy};
use hir::def_id::DefId;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

/* [NOTE:Subst] <via Nico on slack>
   One assumption in `core::ty` is that **every binder is fresh**.
   So `core::ty::Expr` and everything in `core::ty` uses a distinct pure-binder
   which is just a wrapper over an integer (except that we also keep the source
   level binder around for error reporting).

   `Subst` maps the source `ast` level binder to the freshly generated `core::ty`
   binder

   We generate fresh names for function level binders using the `IndexGen` as shown

        let fresh = name_gen.fresh()
*/

/* [NOTE:Existential-Binders] <via Nico on slack>
   The binder in an existential can shadow function level binders and core
   is sort of locally nameless so we generate a `ty::Var::Bound` for those as shown
   in the `ast::TyKind::Exists { bind, path, pred }` case of `resolve_ty`.
   The `0` in `ty::Var::Bound(0)` is related to structs not to the debruijn index.
   Existentials are the only thing nameless so we don't keep track of Debruijn
   indices, that's why it's only sort of locally nameless.
*/

pub struct Subst {
    exprs: ScopeMap<Symbol, ty::Var>,
    locs: FxHashMap<Symbol, Name>,
    types: ScopeMap<DefId, ParamTy>,
}

impl Subst {
    pub(crate) fn new() -> Self {
        Self { exprs: ScopeMap::new(), locs: FxHashMap::default(), types: ScopeMap::new() }
    }

    pub(crate) fn push_expr_layer(&mut self) {
        self.exprs.push_layer();
    }

    pub(crate) fn pop_expr_layer(&mut self) {
        self.exprs.pop_layer();
    }

    pub(crate) fn insert_expr(&mut self, symb: Symbol, name: ty::Var) -> Option<ty::Var> {
        if self.exprs.contains_key_at_top(&symb) {
            self.exprs.get(&symb).copied()
        } else {
            self.exprs.define(symb, name);
            None
        }
    }

    pub(crate) fn insert_loc(&mut self, symb: Symbol, name: Name) -> Option<Name> {
        self.locs.insert(symb, name)
    }

    pub(crate) fn insert_type(&mut self, did: DefId, name: Symbol) {
        let index = self.types.len() as u32;
        let param_ty = ty::ParamTy { index, name };
        assert!(!self.types.contains_key_at_top(&did));
        self.types.define(did, param_ty);
    }

    pub(crate) fn insert_generic_types(&mut self, tcx: TyCtxt, generics: &hir::Generics) {
        for param in generics.params {
            if let hir::GenericParamKind::Type { .. } = param.kind {
                let def_id = tcx.hir().local_def_id(param.hir_id).to_def_id();
                let name = param.name.ident().name;
                self.insert_type(def_id, name);
            }
        }
    }

    pub(crate) fn push_type_layer(&mut self) {
        self.types.push_layer();
    }

    pub(crate) fn get_expr(&self, symb: Symbol) -> Option<ty::Var> {
        self.exprs.get(&symb).copied()
    }

    pub(crate) fn get_loc(&self, symb: Symbol) -> Option<Name> {
        self.locs.get(&symb).copied()
    }

    pub(crate) fn get_param_ty(&self, did: DefId) -> Option<ParamTy> {
        self.types.get(&did).copied()
    }
}
