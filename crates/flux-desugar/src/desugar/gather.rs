//! Gathering is the process of traversing a type to collect parameters.
//!
//! A parameter can be declared explicitly with a sort as in `fn<refine n: int>(i32[n])` or implicitly
//! with the `@` or `#` syntax, e.g., `fn foo(&i32[@n])`.
use flux_common::iter::IterExt;
use flux_errors::FluxSession;
use flux_middle::fhir;
use flux_syntax::surface;
use rustc_data_structures::fx::{FxIndexMap, IndexEntry};
use rustc_errors::ErrorGuaranteed;

use super::{
    errors::{DuplicateParam, IllegalBinder},
    DesugarCtxt, Env,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

/// A position within a type to track where binders are allowed.
#[derive(Clone, Copy)]
enum TypePos {
    /// Type in input position allowing `@n` binders
    Input,
    /// Type in output position allowing `#n` binders
    Output,
    /// A struct field which disallow implicit parameters.
    Field,
    /// Any other position which doesn't allow binders, e.g., inside generic arguments (except for boxes)
    Other,
}

impl TypePos {
    fn is_binder_allowed(self, kind: surface::BindKind) -> bool {
        match self {
            TypePos::Input => matches!(kind, surface::BindKind::At),
            TypePos::Output => matches!(kind, surface::BindKind::Pound),
            TypePos::Field | TypePos::Other => false,
        }
    }
}

#[derive(Default)]
struct Params {
    map: FxIndexMap<surface::Ident, Param>,
}

enum Param {
    Explicit(fhir::Sort),
    At,
    Pound,
    Colon,
    SyntaxError,
}

impl Params {
    pub(crate) fn insert_into_env(self, env: &mut Env) {
        for (ident, param) in self.map {
            let param = match param {
                Param::Explicit(sort) => super::Param::Refined(env.fresh(), sort, false),
                Param::At | Param::Pound | Param::Colon => {
                    super::Param::Refined(env.fresh(), fhir::Sort::Wildcard, true)
                }
                Param::SyntaxError => super::Param::Unrefined,
            };
            env.insert_unchecked(ident, param);
        }
    }
}

impl From<surface::BindKind> for Param {
    fn from(kind: surface::BindKind) -> Self {
        match kind {
            surface::BindKind::At => Param::At,
            surface::BindKind::Pound => Param::Pound,
        }
    }
}

impl Params {
    fn insert(&mut self, sess: &FluxSession, ident: surface::Ident, param: Param) -> Result {
        match self.map.entry(ident) {
            IndexEntry::Occupied(entry) => {
                Err(sess.emit_err(DuplicateParam::new(*entry.key(), ident)))
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(param);
                Ok(())
            }
        }
    }
}

impl DesugarCtxt<'_, '_> {
    /// Implicit parameters are not allowed in struct definition but we traverse it to report errors
    pub(crate) fn gather_params_struct(&self, struct_def: &surface::StructDef) -> Result {
        let mut params = Params::default();
        struct_def
            .fields
            .iter()
            .flatten()
            .try_for_each_exhaust(|ty| {
                self.gather_params_ty(None, ty, TypePos::Field, &mut params)
            })?;
        debug_assert!(params.map.is_empty());
        Ok(())
    }

    pub(crate) fn gather_params_variant(
        &self,
        variant_def: &surface::VariantDef,
        env: &mut Env,
    ) -> Result {
        let mut params = Params::default();
        for ty in &variant_def.fields {
            self.gather_params_ty(None, ty, TypePos::Input, &mut params)?;
        }
        // Traverse `VariantRet` to find illegal binders and report invalid refinement errors.
        self.gather_params_variant_ret(&variant_def.ret, &mut params)?;

        // Check params in `VariantRet`
        variant_def
            .ret
            .indices
            .indices
            .iter()
            .try_for_each_exhaust(|idx| {
                if let surface::RefineArg::Bind(_, kind, span) = idx {
                    Err(self.emit_err(IllegalBinder::new(*span, *kind)))
                } else {
                    Ok(())
                }
            })?;

        params.insert_into_env(env);

        Ok(())
    }

    fn gather_params_variant_ret(&self, ret: &surface::VariantRet, params: &mut Params) -> Result {
        self.gather_params_path(&ret.path, TypePos::Other, params)?;
        self.gather_params_indices(&ret.indices, TypePos::Other, params)
    }

    /// Parameters cannot be defined inside predicates but we traverse it to report errors if we
    /// find them.
    pub(crate) fn gather_params_predicates(
        &self,
        predicates: &[surface::WhereBoundPredicate],
    ) -> Result {
        let mut params = Params::default();
        for predicate in predicates {
            self.gather_params_ty(None, &predicate.bounded_ty, TypePos::Other, &mut params)?;
            for bound in &predicate.bounds {
                self.gather_params_path(&bound.path, TypePos::Other, &mut params)?;
            }
        }
        debug_assert!(params.map.is_empty());
        Ok(())
    }

    pub(crate) fn gather_input_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        env: &mut Env,
    ) -> Result {
        let mut params = Params::default();
        for param in fn_sig.generics.iter().flat_map(|g| &g.params) {
            let surface::GenericParamKind::Refine { sort } = &param.kind else { continue };
            params.insert(
                self.genv.sess,
                param.name,
                Param::Explicit(self.sort_resolver.resolve_sort(sort)?),
            )?;
        }
        for arg in &fn_sig.args {
            self.gather_params_fun_arg(arg, &mut params)?;
        }
        params.insert_into_env(env);
        Ok(())
    }

    pub(crate) fn gather_output_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        env: &mut Env,
    ) -> Result {
        let mut params = Params::default();
        if let surface::FnRetTy::Ty(ty) = &fn_sig.returns {
            self.gather_params_ty(None, ty, TypePos::Output, &mut params)?;
        }
        for cstr in &fn_sig.ensures {
            if let surface::Constraint::Type(_, ty) = cstr {
                self.gather_params_ty(None, ty, TypePos::Output, &mut params)?;
            };
        }
        params.insert_into_env(env);
        Ok(())
    }

    fn gather_params_fun_arg(&self, arg: &surface::Arg, params: &mut Params) -> Result {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                params.insert(self.genv.sess, *bind, Param::Colon)?;
                self.gather_params_path(path, TypePos::Input, params)?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                params.insert(self.genv.sess, *loc, Param::Explicit(fhir::Sort::Loc))?;
                self.gather_params_ty(None, ty, TypePos::Input, params)?;
            }
            surface::Arg::Ty(bind, ty) => {
                self.gather_params_ty(*bind, ty, TypePos::Input, params)?;
            }
        }
        Ok(())
    }

    fn gather_params_ty(
        &self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        pos: TypePos,
        params: &mut Params,
    ) -> Result {
        match &ty.kind {
            surface::TyKind::Indexed { bty, indices } => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                self.gather_params_indices(indices, pos, params)?;
                self.gather_params_bty(bty, pos, params)
            }
            surface::TyKind::Base(bty) => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::Colon)?;
                }
                self.gather_params_bty(bty, pos, params)
            }
            surface::TyKind::Ref(_, ty) | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                self.gather_params_ty(None, ty, pos, params)
            }
            surface::TyKind::Tuple(tys) => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                for ty in tys {
                    self.gather_params_ty(None, ty, pos, params)?;
                }
                Ok(())
            }
            surface::TyKind::Array(ty, _) => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                self.gather_params_ty(None, ty, TypePos::Other, params)
            }
            surface::TyKind::Exists { bty, .. } => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                self.gather_params_bty(bty, pos, params)
            }
            surface::TyKind::GeneralExists { ty, .. } => {
                if let Some(bind) = bind {
                    params.insert(self.genv.sess, bind, Param::SyntaxError)?;
                }
                // Declaring parameters with @ inside and existential has weird behavior if names
                // are being shadowed. Thus, we don't allow it to keep things simple. We could eventually
                // allow it if we resolve the weird behavior by detecting shadowing.
                self.gather_params_ty(None, ty, TypePos::Other, params)
            }
            surface::TyKind::ImplTrait(_, bounds) => {
                for bound in bounds {
                    self.gather_params_path(&bound.path, TypePos::Other, params)?;
                }
                Ok(())
            }
        }
    }

    fn gather_params_indices(
        &self,
        indices: &surface::Indices,
        pos: TypePos,
        params: &mut Params,
    ) -> Result {
        for idx in &indices.indices {
            if let surface::RefineArg::Bind(ident, kind, span) = idx {
                if !pos.is_binder_allowed(*kind) {
                    return Err(self.emit_err(IllegalBinder::new(*span, *kind)));
                }
                params.insert(self.genv.sess, *ident, (*kind).into())?;
            }
        }
        Ok(())
    }

    fn gather_params_path(
        &self,
        path: &surface::Path,
        pos: TypePos,
        params: &mut Params,
    ) -> Result {
        // CODESYNC(type-holes, 3) type holes do not have a corresponding `Res`.
        if path.is_hole() {
            return Ok(());
        }

        // Check refinement args
        for arg in &path.refine {
            if let surface::RefineArg::Bind(_, kind, span) = arg {
                return Err(self.emit_err(IllegalBinder::new(*span, *kind)));
            }
        }

        // Check generic args
        let res = self.resolver_output.path_res_map[&path.node_id];
        let pos = if self.genv.is_box(res) { pos } else { TypePos::Other };
        path.generics
            .iter()
            .try_for_each_exhaust(|arg| self.gather_params_generic_arg(arg, pos, params))
    }

    fn gather_params_generic_arg(
        &self,
        arg: &surface::GenericArg,
        pos: TypePos,
        params: &mut Params,
    ) -> Result {
        match arg {
            surface::GenericArg::Type(ty) => self.gather_params_ty(None, ty, pos, params),
            surface::GenericArg::Constraint(_, ty) => self.gather_params_ty(None, ty, pos, params),
        }
    }

    fn gather_params_bty(
        &self,
        bty: &surface::BaseTy,
        pos: TypePos,
        params: &mut Params,
    ) -> Result {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.gather_params_path(path, pos, params),
            surface::BaseTyKind::Slice(ty) => {
                self.gather_params_ty(None, ty, TypePos::Other, params)
            }
        }
    }
}
