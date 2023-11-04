//! Gathering is the process of traversing a type to collect parameters.
//!
//! A parameter can be declared explicitly with a sort as in `fn<refine n: int>(i32[n])` or implicitly
//! with the `@` or `#` syntax, e.g., `fn foo(&i32[@n])`.
use flux_common::{iter::IterExt, span_bug};
use flux_middle::fhir;
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def::DefKind;

use super::{
    errors::{IllegalBinder, RefinedUnrefinableType},
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
    /// Any other position which doesn't allow binders, e.g., inside generic arguments (except for boxes)
    Other,
}

impl TypePos {
    fn is_binder_allowed(self, kind: surface::BindKind) -> bool {
        match self {
            TypePos::Input => matches!(kind, surface::BindKind::At),
            TypePos::Output => matches!(kind, surface::BindKind::Pound),
            TypePos::Other => false,
        }
    }
}

impl DesugarCtxt<'_, '_> {
    pub(crate) fn gather_params_variant(
        &self,
        variant_def: &surface::VariantDef,
        env: &mut Env,
    ) -> Result {
        for ty in &variant_def.fields {
            self.gather_params_ty(None, ty, TypePos::Input, env)?;
        }
        // Traverse `VariantRet` to find illegal binders and report invalid refinement errors.
        self.gather_params_variant_ret(&variant_def.ret, env)?;

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
            })
    }

    fn gather_params_variant_ret(&self, ret: &surface::VariantRet, env: &mut Env) -> Result {
        self.gather_params_path(&ret.path, TypePos::Other, env)?;
        self.gather_params_indices(&ret.indices, TypePos::Other, env)
    }

    /// Parameters cannot be defined inside predicates but we traverse it to report errors if we
    /// find them.
    pub(crate) fn gather_params_predicates(
        &self,
        predicates: &[surface::WhereBoundPredicate],
        env: &mut Env,
    ) -> Result {
        for predicate in predicates {
            self.gather_params_ty(None, &predicate.bounded_ty, TypePos::Other, env)?;
            for bound in &predicate.bounds {
                self.gather_params_path(&bound.path, TypePos::Other, env)?;
            }
        }
        Ok(())
    }

    pub(crate) fn gather_input_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        env: &mut Env,
    ) -> Result {
        for param in fn_sig.generics.iter().flat_map(|g| &g.params) {
            let surface::GenericParamKind::Refine { sort } = &param.kind else { continue };
            env.insert_explicit(
                self.genv.sess,
                param.name,
                self.sort_resolver.resolve_sort(sort)?,
            )?;
        }
        for arg in &fn_sig.args {
            self.gather_params_fun_arg(arg, env)?;
        }

        Ok(())
    }

    pub(crate) fn gather_output_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        env: &mut Env,
    ) -> Result {
        if let surface::FnRetTy::Ty(ty) = &fn_sig.returns {
            self.gather_params_ty(None, ty, TypePos::Output, env)?;
        }
        for cstr in &fn_sig.ensures {
            if let surface::Constraint::Type(_, ty) = cstr {
                self.gather_params_ty(None, ty, TypePos::Output, env)?;
            };
        }
        Ok(())
    }

    fn gather_params_fun_arg(&self, arg: &surface::Arg, env: &mut Env) -> Result {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                if self.path_is_refinable(path) {
                    env.insert_implicit(self.genv.sess, *bind)?;
                } else {
                    return Err(self.emit_err(RefinedUnrefinableType::new(path.span)));
                }
                self.gather_params_path(path, TypePos::Input, env)?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                env.insert_implicit(self.genv.sess, *loc)?;
                self.gather_params_ty(None, ty, TypePos::Input, env)?;
            }
            surface::Arg::Ty(bind, ty) => {
                self.gather_params_ty(*bind, ty, TypePos::Input, env)?;
            }
        }
        Ok(())
    }

    fn gather_params_ty(
        &self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        pos: TypePos,
        env: &mut Env,
    ) -> Result {
        match &ty.kind {
            surface::TyKind::Indexed { bty, indices } => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                if self.bty_is_refinable(bty) {
                    self.gather_params_indices(indices, pos, env)?;
                } else {
                    Err(self.emit_err(RefinedUnrefinableType::new(ty.span)))?;
                }
                self.gather_params_bty(bty, pos, env)
            }
            surface::TyKind::Base(bty) => {
                if let Some(bind) = bind {
                    if self.bty_is_refinable(bty) {
                        env.insert_implicit(self.genv.sess, bind)?;
                    } else {
                        env.insert_unrefined(self.genv.sess, bind)?;
                    }
                }
                self.gather_params_bty(bty, pos, env)
            }
            surface::TyKind::Ref(_, ty) | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                self.gather_params_ty(None, ty, pos, env)
            }
            surface::TyKind::Tuple(tys) => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                for ty in tys {
                    self.gather_params_ty(None, ty, pos, env)?;
                }
                Ok(())
            }
            surface::TyKind::Array(ty, _) => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                self.gather_params_ty(None, ty, TypePos::Other, env)
            }
            surface::TyKind::Exists { bty, .. } => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                self.gather_params_bty(bty, pos, env)
            }
            surface::TyKind::GeneralExists { ty, .. } => {
                if let Some(bind) = bind {
                    env.insert_unrefined(self.genv.sess, bind)?;
                }
                // Declaring parameters with @ inside and existential has weird behavior if names
                // are being shadowed. Thus, we don't allow it to keep things simple. We could eventually
                // allow it if we resolve the weird behavior by detecting shadowing.
                self.gather_params_ty(None, ty, TypePos::Other, env)
            }
            surface::TyKind::ImplTrait(_, bounds) => {
                for bound in bounds {
                    self.gather_params_path(&bound.path, TypePos::Other, env)?;
                }
                Ok(())
            }
        }
    }

    fn gather_params_indices(
        &self,
        indices: &surface::Indices,
        pos: TypePos,
        env: &mut Env,
    ) -> Result {
        if let [surface::RefineArg::Bind(ident, kind, span)] = indices.indices[..] {
            if !pos.is_binder_allowed(kind) {
                return Err(self.emit_err(IllegalBinder::new(span, kind)));
            }
            env.insert_implicit(self.genv.sess, ident)?;
        } else {
            for idx in &indices.indices {
                if let surface::RefineArg::Bind(ident, kind, span) = idx {
                    if !pos.is_binder_allowed(*kind) {
                        return Err(self.emit_err(IllegalBinder::new(*span, *kind)));
                    }
                    env.insert_implicit(self.genv.sess, *ident)?;
                }
            }
        }
        Ok(())
    }

    fn gather_params_path(&self, path: &surface::Path, pos: TypePos, env: &mut Env) -> Result {
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
            .try_for_each_exhaust(|arg| self.gather_params_generic_arg(arg, pos, env))
    }

    fn gather_params_generic_arg(
        &self,
        arg: &surface::GenericArg,
        pos: TypePos,
        env: &mut Env,
    ) -> Result {
        match arg {
            surface::GenericArg::Type(ty) => self.gather_params_ty(None, ty, pos, env),
            surface::GenericArg::Constraint(_, ty) => self.gather_params_ty(None, ty, pos, env),
        }
    }

    fn gather_params_bty(&self, bty: &surface::BaseTy, pos: TypePos, env: &mut Env) -> Result {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.gather_params_path(path, pos, env),
            surface::BaseTyKind::Slice(ty) => self.gather_params_ty(None, ty, TypePos::Other, env),
        }
    }

    fn bty_is_refinable(&self, ty: &surface::BaseTy) -> bool {
        match &ty.kind {
            surface::BaseTyKind::Path(path) => self.path_is_refinable(path),
            surface::BaseTyKind::Slice(_) => true,
        }
    }

    fn path_is_refinable(&self, path: &surface::Path) -> bool {
        let res = self.resolver_output.path_res_map[&path.node_id];
        match res {
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                self.genv.sort_of_generic_param(def_id).is_some()
            }
            fhir::Res::Def(DefKind::TyAlias { .. } | DefKind::Enum | DefKind::Struct, _)
            | fhir::Res::PrimTy(_) => true,
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                self.genv.sort_of_self_ty_alias(alias_to).is_some()
            }
            fhir::Res::SelfTyParam { .. } => false,
            fhir::Res::Def(..) => span_bug!(path.span, "unexpected res `{res:?}`"),
        }
    }
}
