mod env;
mod gather;
use std::iter;

use flux_common::{bug, index::IndexGen, iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, lift::LiftCtxt, ExprKind, FhirId, FluxOwnerId, Res},
    global_env::{self, GlobalEnv},
    try_alloc_slice, ResolverOutput,
};
use flux_syntax::surface;
use hir::{def::DefKind, ItemKind};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::OwnerId;
use rustc_middle::ty::TyCtxt;
use rustc_span::{
    def_id::{DefId, LocalDefId},
    sym::{self},
    symbol::kw,
    Span, Symbol,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

use self::env::{Scope, ScopeId};
use crate::{
    errors,
    sort_resolver::{SelfRes, SortResolver, SORTS},
};

pub(crate) fn desugar_qualifier<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &ResolverOutput,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier<'genv>> {
    let sort_params = &[];
    let sort_resolver = SortResolver::with_sort_params(genv, resolver_output, sort_params);

    let mut env = Env::from_params(&sort_resolver, ScopeId::Misc, &qualifier.args)?;

    let cx = FluxItemCtxt::new(genv, resolver_output, qualifier.name.name);
    let expr = cx.desugar_expr(&mut env, &qualifier.expr);

    Ok(fhir::Qualifier {
        name: qualifier.name.name,
        args: env.into_root().into_params(&cx),
        global: qualifier.global,
        expr: expr?,
    })
}

pub(crate) fn desugar_defn<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &ResolverOutput,
    defn: &surface::FuncDef,
) -> Result<Option<fhir::Defn<'genv>>> {
    if let Some(body) = &defn.body {
        let sort_params = defn.sort_vars.iter().map(|ident| ident.name).collect_vec();
        let sort_resolver = SortResolver::with_sort_params(genv, resolver_output, &sort_params);
        let mut env = Env::from_params(&sort_resolver, ScopeId::Misc, &defn.args)?;

        let cx = FluxItemCtxt::new(genv, resolver_output, defn.name.name);
        let expr = cx.desugar_expr(&mut env, body)?;
        let name = defn.name.name;
        let params = defn.sort_vars.len();
        let sort = sort_resolver.resolve_sort(&defn.output)?;
        let args = env.into_root().into_params(&cx);

        Ok(Some(fhir::Defn { name, params, args, sort, expr }))
    } else {
        Ok(None)
    }
}

pub fn func_def_to_func_decl<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &ResolverOutput,
    defn: &surface::FuncDef,
) -> Result<fhir::FuncDecl<'genv>> {
    let params = defn.sort_vars.len();
    let sort_vars = defn.sort_vars.iter().map(|ident| ident.name).collect_vec();
    let sr = SortResolver::with_sort_params(genv, resolver_output, &sort_vars);
    let inputs_and_output = try_alloc_slice!(
        genv,
        cap: defn.args.len() + 1,
        defn.args
            .iter()
            .map(|arg| &arg.sort)
            .chain(iter::once(&defn.output))
            .map(|sort| sr.resolve_sort(sort))
    )?;
    let sort = fhir::PolyFuncSort::new(params, inputs_and_output);
    let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
    Ok(fhir::FuncDecl { name: defn.name.name, sort, kind })
}

fn gather_refined_by_sort_vars(
    generics: &rustc_middle::ty::Generics,
    refined_by: &surface::RefinedBy,
) -> Vec<Symbol> {
    struct IdentCollector {
        found: FxHashSet<Symbol>,
    }
    impl surface::visit::Visitor for IdentCollector {
        fn visit_base_sort(&mut self, bsort: &surface::BaseSort) {
            if let surface::BaseSort::Ident(x) = bsort {
                self.found.insert(x.name);
            }
            surface::visit::walk_base_sort(self, bsort);
        }
    }
    let mut vis = IdentCollector { found: FxHashSet::default() };
    surface::visit::Visitor::visit_refined_by(&mut vis, refined_by);
    generics
        .params
        .iter()
        .filter_map(|param| if vis.found.contains(&param.name) { Some(param.name) } else { None })
        .collect()
}

pub(crate) struct RustItemCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
    resolver_output: &'a ResolverOutput,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    sort_resolver: SortResolver<'a, 'genv, 'tcx>,
}

type Env<'genv> = env::Env<Param<'genv>>;

#[derive(Debug, Clone)]
struct Param<'fhir> {
    name: fhir::Name,
    sort: fhir::Sort<'fhir>,
    kind: fhir::ParamKind,
    span: Span,
}

struct FluxItemCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    resolver_output: &'a ResolverOutput,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: Symbol,
}

enum FuncRes {
    Param(fhir::Ident),
    Global(fhir::FuncKind),
}

enum QPathRes {
    Param(fhir::Ident),
    Const(DefId),
    NumConst(i128),
}

fn self_res(tcx: TyCtxt, owner: OwnerId) -> SelfRes {
    let def_id = owner.def_id.to_def_id();
    let mut opt_def_id = Some(def_id);
    while let Some(def_id) = opt_def_id {
        match tcx.def_kind(def_id) {
            DefKind::Trait => return SelfRes::Param { trait_id: def_id },
            DefKind::Impl { .. } => return SelfRes::Alias { alias_to: def_id },
            _ => {
                opt_def_id = tcx.opt_parent(def_id);
            }
        }
    }
    SelfRes::None
}

impl<'a, 'genv, 'tcx> RustItemCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        owner: OwnerId,
        resolver_output: &'a ResolverOutput,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    ) -> Self {
        let generics = genv.tcx().generics_of(owner);
        let self_res = self_res(genv.tcx(), owner);
        let sort_resolver = SortResolver::with_generics(genv, resolver_output, generics, self_res);
        RustItemCtxt {
            genv,
            owner,
            local_id_gen: IndexGen::new(),
            sort_resolver,
            resolver_output,
            opaque_tys,
        }
    }

    fn with_new_owner<'b>(&'b mut self, owner: OwnerId) -> RustItemCtxt<'b, 'genv, 'tcx> {
        RustItemCtxt::new(self.genv, owner, self.resolver_output, self.opaque_tys.as_deref_mut())
    }

    fn as_lift_cx<'b>(&'b mut self) -> LiftCtxt<'b, 'genv, 'tcx> {
        LiftCtxt::new(self.genv, self.owner, &self.local_id_gen, self.opaque_tys.as_deref_mut())
    }

    pub(crate) fn desugar_trait(&mut self, trait_: &surface::Trait) -> Result<fhir::Trait<'genv>> {
        let mut env = Env::new(ScopeId::Trait);
        let generics = if let Some(generics) = &trait_.generics {
            self.desugar_generics(generics, &mut env)?
        } else {
            self.as_lift_cx().lift_generics()?
        };
        let assoc_predicates = self.desugar_trait_assoc_predicates(&trait_.assoc_predicates)?;
        Ok(fhir::Trait { generics, assoc_predicates })
    }

    fn desugar_trait_assoc_predicates(
        &self,
        assoc_predicates: &[surface::TraitAssocPredicate],
    ) -> Result<&'genv [fhir::TraitAssocPredicate<'genv>]> {
        try_alloc_slice!(self.genv, assoc_predicates, |assoc_pred| {
            let name = assoc_pred.name.name;
            let sort = self.sort_resolver.resolve_sort(&assoc_pred.sort)?;
            if let fhir::Sort::Func(func_sort) = sort
                && let fhir::Sort::Bool = func_sort.fsort.output()
                && func_sort.params == 0
            {
                Ok(fhir::TraitAssocPredicate { name, sort: func_sort.fsort, span: assoc_pred.span })
            } else {
                Err(self.emit_err(errors::InvalidAssocPredicate::new(assoc_pred.span, name)))
            }
        })
    }

    pub(crate) fn desugar_impl(&mut self, impl_: &surface::Impl) -> Result<fhir::Impl<'genv>> {
        let mut env = Env::new(ScopeId::Impl);
        let generics = if let Some(generics) = &impl_.generics {
            self.desugar_generics(generics, &mut env)?
        } else {
            self.as_lift_cx().lift_generics()?
        };
        let assoc_predicates = self.desugar_impl_assoc_predicates(&impl_.assoc_predicates)?;
        Ok(fhir::Impl { generics, assoc_predicates, extern_id: impl_.extern_id })
    }

    fn desugar_impl_assoc_predicates(
        &self,
        assoc_predicates: &[surface::ImplAssocPredicate],
    ) -> Result<&'genv [fhir::ImplAssocPredicate<'genv>]> {
        try_alloc_slice!(self.genv, assoc_predicates, |assoc_pred| {
            let name = assoc_pred.name.name;
            let mut env = Env::from_params(&self.sort_resolver, ScopeId::Misc, &assoc_pred.params)?;
            let body = self.desugar_expr(&mut env, &assoc_pred.body)?;
            let params = env.into_root().into_params(self);
            Ok(fhir::ImplAssocPredicate { name, params, body, span: assoc_pred.span })
        })
    }

    fn desugar_generics(
        &mut self,
        generics: &surface::Generics,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Generics<'genv>> {
        let hir_generics = self.genv.hir().get_generics(self.owner.def_id).unwrap();

        // 1. Collect generic type parameters by their name
        let hir_params_map: FxHashMap<_, _> = hir_generics
            .params
            .iter()
            .flat_map(|param| {
                if let hir::ParamName::Plain(name) = param.name
                    && let hir::GenericParamKind::Type { default, .. } = param.kind
                {
                    Some((name, (param.def_id, default)))
                } else {
                    None
                }
            })
            .collect();

        // 2. Desugar surface params and resolve them to its corresponding def id or self param.
        let mut surface_params = FxHashMap::default();
        let mut self_kind = None;
        for param in &generics.params {
            if let surface::GenericParamKind::Refine { .. } = &param.kind {
                continue;
            }

            if param.name.name == kw::SelfUpper {
                let kind = match &param.kind {
                    surface::GenericParamKind::Type => {
                        fhir::GenericParamKind::Type { default: None }
                    }
                    surface::GenericParamKind::Spl => fhir::GenericParamKind::SplTy,
                    surface::GenericParamKind::Base => fhir::GenericParamKind::BaseTy,
                    surface::GenericParamKind::Refine { .. } => unreachable!(),
                };
                self_kind = Some(kind);
            } else {
                let Some(&(def_id, default)) = hir_params_map.get(&param.name) else {
                    return Err(self.emit_err(errors::UnresolvedGenericParam::new(param.name)));
                };

                let kind = match &param.kind {
                    surface::GenericParamKind::Type => {
                        fhir::GenericParamKind::Type {
                            default: default
                                .map(|ty| self.as_lift_cx().lift_ty(ty))
                                .transpose()?,
                        }
                    }
                    surface::GenericParamKind::Base => fhir::GenericParamKind::BaseTy,
                    surface::GenericParamKind::Spl => fhir::GenericParamKind::SplTy,
                    surface::GenericParamKind::Refine { .. } => unreachable!(),
                };
                surface_params.insert(def_id, fhir::GenericParam { def_id, kind });
            }
        }

        // 3. Return desugared generic if we have one or else lift it from hir
        let params = try_alloc_slice!(self.genv, hir_generics.params, |hir_param| {
            if let Some(surface_param) = surface_params.remove(&hir_param.def_id) {
                Ok(surface_param)
            } else {
                self.as_lift_cx().lift_generic_param(hir_param)
            }
        })?;

        let predicates = self.desugar_generic_predicates(&generics.predicates, env)?;
        Ok(fhir::Generics { params, self_kind, refinement_params: &[], predicates })
    }

    fn desugar_generic_predicates(
        &mut self,
        predicates: &[surface::WhereBoundPredicate],
        env: &mut Env<'genv>,
    ) -> Result<&'genv [fhir::WhereBoundPredicate<'genv>]> {
        try_alloc_slice!(self.genv, predicates, |pred| {
            let bounded_ty = self.desugar_ty(None, &pred.bounded_ty, env)?;
            let bounds = self.desugar_generic_bounds(&pred.bounds, env)?;
            Ok(fhir::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
        })
    }

    fn desugar_generic_bounds(
        &mut self,
        bounds: &surface::GenericBounds,
        env: &mut Env<'genv>,
    ) -> Result<fhir::GenericBounds<'genv>> {
        try_alloc_slice!(self.genv, bounds, |bound| {
            Ok(fhir::GenericBound::Trait(
                self.desugar_trait_ref(bound, env)?,
                fhir::TraitBoundModifier::None,
            ))
        })
    }

    fn desugar_trait_ref(
        &mut self,
        trait_ref: &surface::TraitRef,
        env: &mut Env<'genv>,
    ) -> Result<fhir::PolyTraitRef<'genv>> {
        Ok(fhir::PolyTraitRef {
            bound_generic_params: &[],
            trait_ref: self.desugar_path(&trait_ref.path, env)?,
        })
    }

    fn desugar_refined_by(
        &mut self,
        refined_by: &surface::RefinedBy,
    ) -> Result<fhir::RefinedBy<'genv>> {
        let generics = self.genv.tcx().generics_of(self.owner);
        let sort_vars = gather_refined_by_sort_vars(generics, refined_by);
        let sr = SortResolver::with_sort_params(self.genv, self.resolver_output, &sort_vars);

        let index_params: Vec<_> = refined_by
            .index_params
            .iter()
            .map(|param| Ok((param.name.name, sr.resolve_sort(&param.sort)?)))
            .try_collect_exhaust()?;

        let generic_idx: FxHashMap<Symbol, hir::def_id::DefId> = generics
            .params
            .iter()
            .map(|param| (param.name, param.def_id))
            .collect();
        let sort_params = sort_vars.iter().map(|sym| generic_idx[&sym]).collect();

        Ok(fhir::RefinedBy::new(self.owner.def_id, index_params, sort_params, refined_by.span))
    }

    pub(crate) fn desugar_struct_def(
        &mut self,
        struct_def: &surface::StructDef,
    ) -> Result<fhir::StructDef<'genv>> {
        let mut env = self.gather_params_struct(struct_def)?;

        let refined_by = if let Some(refined_by) = &struct_def.refined_by {
            self.desugar_refined_by(refined_by)?
        } else {
            self.as_lift_cx().lift_refined_by()
        };

        let generics =
            self.desugar_generics_for_adt(struct_def.generics.as_ref(), &refined_by, &mut env)?;

        let invariants = try_alloc_slice!(self.genv, &struct_def.invariants, |invariant| {
            self.desugar_expr(&mut env, invariant)
        })?;

        let kind = if struct_def.opaque {
            fhir::StructKind::Opaque
        } else {
            let hir::ItemKind::Struct(variant_data, _) =
                &self.genv.hir().expect_item(self.owner.def_id).kind
            else {
                bug!("expected struct")
            };
            debug_assert_eq!(struct_def.fields.len(), variant_data.fields().len());
            let fields = try_alloc_slice!(
                self.genv,
                iter::zip(&struct_def.fields, variant_data.fields()),
                |(ty, hir_field)| {
                    if let Some(ty) = ty {
                        Ok(fhir::FieldDef {
                            ty: self.desugar_ty(None, ty, &mut env)?,
                            def_id: hir_field.def_id,
                            lifted: false,
                        })
                    } else {
                        self.as_lift_cx().lift_field_def(hir_field)
                    }
                },
            )?;
            fhir::StructKind::Transparent { fields }
        };
        let struct_def = fhir::StructDef {
            owner_id: self.owner,
            generics,
            refined_by: self.genv.alloc(refined_by),
            params: env.into_root().into_params(self),
            kind,
            invariants,
            extern_id: struct_def.extern_id,
        };
        Ok(struct_def)
    }

    pub(crate) fn desugar_enum_def(
        &mut self,
        enum_def: &surface::EnumDef,
    ) -> Result<fhir::EnumDef<'genv>> {
        let def_id = self.owner.def_id;
        let ItemKind::Enum(hir_enum, _) = self.genv.hir().expect_item(def_id).kind else {
            bug!("expected enum");
        };
        let variants = try_alloc_slice!(
            self.genv,
            iter::zip(&enum_def.variants, hir_enum.variants),
            |(variant, hir_variant)| self.desugar_enum_variant_def(variant, hir_variant)
        )?;

        let mut env = Env::from_params(
            &self.sort_resolver,
            ScopeId::Enum,
            enum_def.refined_by.iter().flat_map(|it| &it.index_params),
        )?;

        let refined_by = if let Some(refined_by) = &enum_def.refined_by {
            self.desugar_refined_by(refined_by)?
        } else {
            self.as_lift_cx().lift_refined_by()
        };

        let generics =
            self.desugar_generics_for_adt(enum_def.generics.as_ref(), &refined_by, &mut env)?;

        let invariants = try_alloc_slice!(self.genv, &enum_def.invariants, |invariant| {
            self.desugar_expr(&mut env, invariant)
        })?;

        let enum_def = fhir::EnumDef {
            owner_id: self.owner,
            generics,
            refined_by: self.genv.alloc(refined_by),
            params: env.into_root().into_params(self),
            variants,
            invariants,
            extern_id: enum_def.extern_id,
        };
        Ok(enum_def)
    }

    fn desugar_enum_variant_def(
        &mut self,
        variant_def: &Option<surface::VariantDef>,
        hir_variant: &hir::Variant,
    ) -> Result<fhir::VariantDef<'genv>> {
        if let Some(variant_def) = variant_def {
            let mut env = self.gather_params_variant(variant_def)?;

            let fields = try_alloc_slice!(
                self.genv,
                iter::zip(&variant_def.fields, hir_variant.data.fields()),
                |(ty, hir_field)| {
                    Ok(fhir::FieldDef {
                        ty: self.desugar_ty(None, ty, &mut env)?,
                        def_id: hir_field.def_id,
                        lifted: false,
                    })
                }
            )?;

            let ret = if let Some(ret) = &variant_def.ret {
                self.desugar_variant_ret(ret, &mut env)?
            } else {
                self.as_lift_cx().lift_variant_ret()
            };

            Ok(fhir::VariantDef {
                def_id: hir_variant.def_id,
                params: env.into_root().into_params(self),
                fields,
                ret,
                span: variant_def.span,
                lifted: false,
            })
        } else {
            self.as_lift_cx().lift_enum_variant(hir_variant)
        }
    }

    fn desugar_generics_for_adt(
        &mut self,
        generics: Option<&surface::Generics>,
        refined_by: &fhir::RefinedBy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Generics<'genv>> {
        Ok(if let Some(generics) = generics {
            self.desugar_generics(generics, env)?
        } else {
            self.as_lift_cx().lift_generics()?
        }
        .with_refined_by(self.genv, refined_by))
    }

    pub(crate) fn desugar_type_alias(
        &mut self,
        ty_alias: Option<&surface::TyAlias>,
    ) -> Result<fhir::TyAlias<'genv>> {
        let Some(ty_alias) = ty_alias else {
            return self.as_lift_cx().lift_type_alias();
        };

        let mut env = self.gather_params_type_alias(ty_alias)?;

        let refined_by = self.desugar_refined_by(&ty_alias.refined_by)?;
        let mut generics = self.desugar_generics(&ty_alias.generics, &mut env)?;

        let ty = self.desugar_ty(None, &ty_alias.ty, &mut env)?;

        let params = env.into_root().into_params(self);
        let idx = params.len() - ty_alias.refined_by.index_params.len();
        let (refinement_params, index_params) = params.split_at(idx);
        generics.refinement_params = refinement_params;

        let ty_alias = fhir::TyAlias {
            owner_id: self.owner,
            refined_by: self.genv.alloc(refined_by),
            generics,
            index_params,
            ty,
            span: ty_alias.span,
            lifted: false,
        };
        Ok(ty_alias)
    }

    pub(crate) fn desugar_assoc_type(&mut self) -> Result<fhir::AssocType<'genv>> {
        let generics = self.as_lift_cx().lift_generics()?;
        Ok(fhir::AssocType { generics })
    }

    pub(crate) fn desugar_fn_sig(
        &mut self,
        fn_sig: Option<&surface::FnSig>,
    ) -> Result<fhir::FnSig<'genv>> {
        let Some(fn_sig) = fn_sig else {
            return self.as_lift_cx().lift_fn_sig();
        };

        let mut env = self.gather_params_fn_sig(fn_sig)?;

        let mut requires = vec![];

        // Desugar generics after we have gathered the input params
        let mut generics = self.desugar_generics(&fn_sig.generics, &mut env)?;

        if let Some(e) = &fn_sig.requires {
            let pred = self.desugar_expr(&mut env, e)?;
            requires.push(fhir::Constraint::Pred(pred));
        }

        // Bail out if there's an error in the arguments to avoid confusing error messages
        let args = try_alloc_slice!(self.genv, &fn_sig.args, |arg| {
            self.desugar_fun_arg(arg, &mut env, &mut requires)
        })?;

        // Desugar output
        env.enter(ScopeId::FnOutput);
        let ret = self.desugar_asyncness(fn_sig.asyncness, &fn_sig.returns, &mut env);

        let ensures = try_alloc_slice!(self.genv, &fn_sig.ensures, |cstr| {
            self.desugar_constraint(cstr, &mut env)
        })?;

        let output = fhir::FnOutput { params: env.pop().into_params(self), ret: ret?, ensures };

        generics.refinement_params = env.into_root().into_params(self);

        let fn_sig = fhir::FnSig {
            generics,
            requires: self.genv.alloc_slice(&requires),
            args,
            output,
            span: fn_sig.span,
            lifted: false,
        };
        Ok(fn_sig)
    }

    fn desugar_constraint(
        &mut self,
        cstr: &surface::Constraint,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Constraint<'genv>> {
        match cstr {
            surface::Constraint::Type(bind, ty) => {
                let (idx, loc) = self.resolve_loc(env, *bind)?;
                let ty = self.desugar_ty(None, ty, env)?;
                Ok(fhir::Constraint::Type(loc, ty, idx))
            }
            surface::Constraint::Pred(e) => {
                let pred = self.desugar_expr(env, e)?;
                Ok(fhir::Constraint::Pred(pred))
            }
        }
    }

    fn desugar_fun_arg(
        &mut self,
        arg: &surface::Arg,
        env: &mut Env<'genv>,
        requires: &mut Vec<fhir::Constraint<'genv>>,
    ) -> Result<fhir::Ty<'genv>> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let bty = self.desugar_path_to_bty(path, env)?;

                let pred = self.desugar_expr(env, pred)?;
                let span = pred.span;
                let pred = fhir::Pred {
                    kind: fhir::PredKind::Expr(pred),
                    span,
                    fhir_id: self.next_fhir_id(),
                };

                let ty = if let Some(idx) = self.bind_into_refine_arg(*bind, env)? {
                    fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: path.span }
                } else {
                    fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: path.span }
                };

                let span = path.span.to(pred.span);
                let kind = fhir::TyKind::Constr(pred, self.genv.alloc(ty));
                Ok(fhir::Ty { kind, span })
            }
            surface::Arg::StrgRef(loc, ty) => {
                let span = loc.span;
                let (idx, loc) = self.resolve_loc(env, *loc)?;
                let ty = self.desugar_ty(None, ty, env)?;
                requires.push(fhir::Constraint::Type(loc, ty, idx));
                let kind = fhir::TyKind::Ptr(self.mk_lft_hole(), loc);
                Ok(fhir::Ty { kind, span })
            }
            surface::Arg::Ty(bind, ty) => self.desugar_ty(*bind, ty, env),
        }
    }

    fn desugar_asyncness(
        &mut self,
        asyncness: surface::Async,
        returns: &surface::FnRetTy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Ty<'genv>> {
        match asyncness {
            surface::Async::Yes { node_id, span } => {
                let item_id = self.resolver_output.impl_trait_res_map[&node_id];
                let def_id = item_id.owner_id.def_id;
                let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

                let opaque_ty = self
                    .with_new_owner(item_id.owner_id)
                    .desugar_opaque_ty_for_async(returns, env)?;
                self.insert_opaque_ty(item_id.owner_id.def_id, opaque_ty);

                let (args, _) = self.desugar_generic_args(res, &[], env)?;
                let item_id = hir::ItemId { owner_id: hir::OwnerId { def_id } };
                let refine_args = env.root().to_refine_args(self, span);
                let kind = fhir::TyKind::OpaqueDef(item_id, args, refine_args, false);
                Ok(fhir::Ty { kind, span })
            }
            surface::Async::No => Ok(self.desugar_fn_ret_ty(returns, env)?),
        }
    }

    fn desugar_opaque_ty_for_async(
        &mut self,
        returns: &surface::FnRetTy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::OpaqueTy<'genv>> {
        let output = self.desugar_fn_ret_ty(returns, env)?;
        // Does this opaque type has any generics?
        let generics = self.as_lift_cx().lift_generics()?;
        let bound = fhir::GenericBound::LangItemTrait(
            hir::LangItem::Future,
            &[],
            self.genv.alloc_slice(&[fhir::TypeBinding {
                ident: surface::Ident::with_dummy_span(sym::Output),
                term: output,
            }]),
        );
        Ok(fhir::OpaqueTy { generics, bounds: self.genv.alloc_slice(&[bound]) })
    }

    fn desugar_fn_ret_ty(
        &mut self,
        returns: &surface::FnRetTy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Ty<'genv>> {
        match returns {
            surface::FnRetTy::Ty(ty) => self.desugar_ty(None, ty, env),
            surface::FnRetTy::Default(span) => {
                let kind = fhir::TyKind::Tuple(&[]);
                Ok(fhir::Ty { kind, span: *span })
            }
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Ty<'genv>> {
        let node_id = ty.node_id;
        let span = ty.span;
        let kind = match &ty.kind {
            surface::TyKind::Base(bty) => {
                // CODESYNC(type-holes, 3)
                if let surface::BaseTyKind::Path(path) = &bty.kind
                    && path.is_hole()
                {
                    fhir::TyKind::Hole(self.next_fhir_id())
                } else {
                    return self.desugar_bty_bind(bind, bty, env);
                }
            }
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.desugar_bty(bty, env)?;
                let idx = self.desugar_indices(indices, env)?;
                fhir::TyKind::Indexed(bty, idx)
            }
            surface::TyKind::Exists { bind: ex_bind, bty, pred } => {
                let ty_span = ty.span;
                let bty_span = bty.span;

                env.enter(ScopeId::Exists(node_id));

                let bty = self.desugar_bty(bty, env)?;
                let pred = self.desugar_pred(env, pred)?;

                let params = env.pop().into_params(self);

                let idx = fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(fhir::Expr {
                        kind: fhir::ExprKind::Var(params[0].ident, None),
                        span: ex_bind.span,
                        fhir_id: self.next_fhir_id(),
                    }),
                    span: ex_bind.span,
                    fhir_id: self.next_fhir_id(),
                };
                let indexed = fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: bty_span };
                let constr = fhir::Ty {
                    kind: fhir::TyKind::Constr(pred, self.genv.alloc(indexed)),
                    span: ty_span,
                };
                fhir::TyKind::Exists(params, self.genv.alloc(constr))
            }
            surface::TyKind::GeneralExists { ty, pred, .. } => {
                env.enter(ScopeId::Exists(node_id));
                let mut ty = self.desugar_ty(None, ty, env)?;
                if let Some(pred) = pred {
                    let pred = self.desugar_expr(env, pred)?;
                    let span = ty.span.to(pred.span);
                    let pred = fhir::Pred {
                        kind: fhir::PredKind::Expr(pred),
                        span,
                        fhir_id: self.next_fhir_id(),
                    };
                    ty = fhir::Ty { kind: fhir::TyKind::Constr(pred, self.genv.alloc(ty)), span };
                }
                let params = env.pop().into_params(self);

                fhir::TyKind::Exists(params, self.genv.alloc(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.desugar_pred(env, pred)?;
                let ty = self.desugar_ty(None, ty, env)?;
                fhir::TyKind::Constr(pred, self.genv.alloc(ty))
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let ty = self.desugar_ty(None, ty, env)?;
                let mut_ty = fhir::MutTy { ty: self.genv.alloc(ty), mutbl: *mutbl };
                fhir::TyKind::Ref(self.mk_lft_hole(), mut_ty)
            }
            surface::TyKind::Tuple(tys) => {
                let tys = try_alloc_slice!(self.genv, tys, |ty| self.desugar_ty(None, ty, env))?;
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(None, ty, env)?;
                fhir::TyKind::Array(
                    self.genv.alloc(ty),
                    fhir::ArrayLen { val: len.val, span: len.span },
                )
            }
            surface::TyKind::ImplTrait(node_id, bounds) => {
                let item_id = self.resolver_output.impl_trait_res_map[&node_id];
                let def_id = item_id.owner_id.def_id;
                let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

                let opaque_ty = self
                    .with_new_owner(item_id.owner_id)
                    .desugar_opaque_ty_for_impl_trait(bounds, env)?;
                self.insert_opaque_ty(def_id, opaque_ty);

                let (args, _) = self.desugar_generic_args(res, &[], env)?;
                let refine_args = env.root().to_refine_args(self, ty.span);
                fhir::TyKind::OpaqueDef(item_id, args, refine_args, false)
            }
        };
        Ok(fhir::Ty { kind, span })
    }

    fn desugar_opaque_ty_for_impl_trait(
        &mut self,
        bounds: &surface::GenericBounds,
        env: &mut Env<'genv>,
    ) -> Result<fhir::OpaqueTy<'genv>> {
        let generics = self.as_lift_cx().lift_generics()?;
        let bounds = self.desugar_generic_bounds(bounds, env)?;
        Ok(fhir::OpaqueTy { generics, bounds })
    }

    fn mk_lft_hole(&self) -> fhir::Lifetime {
        fhir::Lifetime::Hole(self.next_fhir_id())
    }

    fn desugar_indices(
        &mut self,
        idxs: &surface::Indices,
        env: &mut Env<'genv>,
    ) -> Result<fhir::RefineArg<'genv>> {
        if let [arg] = &idxs.indices[..] {
            self.desugar_refine_arg(arg, env)
        } else {
            let flds = try_alloc_slice!(self.genv, &idxs.indices, |arg| {
                self.desugar_refine_arg(arg, env)
            })?;
            Ok(fhir::RefineArg {
                kind: fhir::RefineArgKind::Record(flds),
                fhir_id: self.next_fhir_id(),
                span: idxs.span,
            })
        }
    }

    fn desugar_refine_arg(
        &mut self,
        arg: &surface::RefineArg,
        env: &mut Env<'genv>,
    ) -> Result<fhir::RefineArg<'genv>> {
        match arg {
            surface::RefineArg::Bind(ident, ..) => {
                Ok(self.bind_into_refine_arg(*ident, env)?.unwrap())
            }
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(self.desugar_expr(env, expr)?),
                    fhir_id: self.next_fhir_id(),
                    span: expr.span,
                })
            }
            surface::RefineArg::Abs(_, body, node_id, span) => {
                env.enter(ScopeId::Abs(*node_id));
                let body = self.desugar_expr(env, body)?;
                let params = env.pop().into_params(self);
                Ok(fhir::RefineArg {
                    kind: fhir::RefineArgKind::Abs(params, body),
                    fhir_id: self.next_fhir_id(),
                    span: *span,
                })
            }
        }
    }

    fn bind_into_refine_arg(
        &self,
        ident: surface::Ident,
        env: &Env,
    ) -> Result<Option<fhir::RefineArg<'genv>>> {
        match env.get(ident) {
            Some(param) => {
                Ok(Some(fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(fhir::Expr {
                        kind: fhir::ExprKind::Var(
                            fhir::Ident::new(param.name, ident),
                            Some(param.kind),
                        ),
                        span: ident.span,
                        fhir_id: self.next_fhir_id(),
                    }),
                    fhir_id: self.next_fhir_id(),
                    span: ident.span,
                }))
            }
            None => Ok(None),
        }
    }

    fn desugar_bty(
        &mut self,
        bty: &surface::BaseTy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::BaseTy<'genv>> {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.desugar_path_to_bty(path, env),
            surface::BaseTyKind::Slice(ty) => {
                let ty = self.desugar_ty(None, ty, env)?;
                let kind = fhir::BaseTyKind::Slice(self.genv.alloc(ty));
                Ok(fhir::BaseTy { kind, span: bty.span })
            }
        }
    }

    fn desugar_path(
        &mut self,
        path: &surface::Path,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Path<'genv>> {
        let res = self.resolver_output.path_res_map[&path.node_id];
        let (args, bindings) = self.desugar_generic_args(res, &path.generics, env)?;
        let refine =
            try_alloc_slice!(self.genv, &path.refine, |arg| self.desugar_refine_arg(arg, env))?;
        Ok(fhir::Path { res, args, bindings, refine, span: path.span })
    }

    fn desugar_path_to_bty(
        &mut self,
        path: &surface::Path,
        env: &mut Env<'genv>,
    ) -> Result<fhir::BaseTy<'genv>> {
        Ok(fhir::BaseTy::from(fhir::QPath::Resolved(None, self.desugar_path(path, env)?)))
    }

    fn desugar_alias_pred(
        &mut self,
        env: &mut Env<'genv>,
        alias_pred: &surface::AliasPred,
        refine_args: &[surface::RefineArg],
    ) -> Result<fhir::PredKind<'genv>> {
        let path = self.desugar_path(&alias_pred.trait_id, env)?;

        if let Res::Def(DefKind::Trait, trait_id) = path.res {
            let (generic_args, _) = self.desugar_generic_args(path.res, &alias_pred.args, env)?;
            let refine_args =
                try_alloc_slice!(self.genv, refine_args, |arg| self.desugar_refine_arg(arg, env))?;
            let alias_pred = fhir::AliasPred { trait_id, name: alias_pred.name.name, generic_args };
            Ok(fhir::PredKind::Alias(alias_pred, refine_args))
        } else {
            Err(self.emit_err(errors::UnresolvedVar::from_path(&alias_pred.trait_id, "trait")))
        }
    }

    fn desugar_pred(
        &mut self,
        env: &mut Env<'genv>,
        pred: &surface::Pred,
    ) -> Result<fhir::Pred<'genv>> {
        let kind = match &pred.kind {
            surface::PredKind::Expr(expr) => fhir::PredKind::Expr(self.desugar_expr(env, expr)?),
            surface::PredKind::Alias(alias_pred, args) => {
                self.desugar_alias_pred(env, alias_pred, args)?
            }
        };
        let span = pred.span;
        Ok(fhir::Pred { kind, span, fhir_id: self.next_fhir_id() })
    }

    fn desugar_generic_args(
        &mut self,
        res: Res,
        args: &[surface::GenericArg],
        env: &mut Env<'genv>,
    ) -> Result<(&'genv [fhir::GenericArg<'genv>], &'genv [fhir::TypeBinding<'genv>])> {
        let mut fhir_args = vec![];
        let mut bindings = vec![];
        if let Res::Def(
            DefKind::TyAlias { .. } | DefKind::Struct | DefKind::Enum | DefKind::OpaqueTy,
            def_id,
        ) = res
        {
            let generics = self.genv.tcx().generics_of(def_id);
            for param in &generics.params {
                if let rustc_middle::ty::GenericParamDefKind::Lifetime = param.kind {
                    fhir_args.push(fhir::GenericArg::Lifetime(self.mk_lft_hole()));
                }
            }
        }
        for arg in args {
            match arg {
                surface::GenericArg::Type(ty) => {
                    let ty = self.desugar_ty(None, ty, env)?;
                    fhir_args.push(fhir::GenericArg::Type(self.genv.alloc(ty)));
                }
                surface::GenericArg::Constraint(ident, ty) => {
                    bindings.push(fhir::TypeBinding {
                        ident: *ident,
                        term: self.desugar_ty(None, ty, env)?,
                    });
                }
            }
        }
        Ok((self.genv.alloc_slice(&fhir_args), self.genv.alloc_slice(&bindings)))
    }

    fn desugar_bty_bind(
        &mut self,
        bind: Option<surface::Ident>,
        bty: &surface::BaseTy,
        env: &mut Env<'genv>,
    ) -> Result<fhir::Ty<'genv>> {
        let bty = self.desugar_bty(bty, env)?;

        let span = bty.span;
        let kind = if let Some(bind) = bind
            && let Some(idx) = self.bind_into_refine_arg(bind, env)?
        {
            fhir::TyKind::Indexed(bty, idx)
        } else {
            fhir::TyKind::BaseTy(bty)
        };
        Ok(fhir::Ty { kind, span })
    }

    fn desugar_variant_ret(
        &mut self,
        ret: &surface::VariantRet,
        env: &mut Env<'genv>,
    ) -> Result<fhir::VariantRet<'genv>> {
        let bty = self.desugar_path_to_bty(&ret.path, env)?;
        let idx = self.desugar_indices(&ret.indices, env)?;
        Ok(fhir::VariantRet { bty, idx })
    }

    fn insert_opaque_ty(&mut self, def_id: LocalDefId, opaque_ty: fhir::OpaqueTy<'genv>) {
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item {def_id:?}"))
            .insert(def_id, opaque_ty);
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess().emit_err(err)
    }
}

impl<'a, 'genv, 'tcx> FluxItemCtxt<'a, 'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        resolver_output: &'a ResolverOutput,
        owner: Symbol,
    ) -> Self {
        Self { genv, resolver_output, local_id_gen: Default::default(), owner }
    }
}

impl<'genv> Env<'genv> {
    fn from_params<'a>(
        sort_resolver: &SortResolver<'_, 'genv, '_>,
        scope: ScopeId,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<Self> {
        let mut env = Env::new(scope);
        let name_gen = IndexGen::new();
        for param in params {
            let sort = sort_resolver.resolve_sort(&param.sort)?;
            env.insert(
                sort_resolver.genv.sess(),
                param.name,
                Param {
                    name: name_gen.fresh(),
                    sort,
                    kind: fhir::ParamKind::Explicit,
                    span: param.span,
                },
            )?;
        }
        Ok(env)
    }
}

fn desugar_bin_op(op: surface::BinOp) -> fhir::BinOp {
    match op {
        surface::BinOp::Iff => fhir::BinOp::Iff,
        surface::BinOp::Imp => fhir::BinOp::Imp,
        surface::BinOp::Or => fhir::BinOp::Or,
        surface::BinOp::And => fhir::BinOp::And,
        surface::BinOp::Eq => fhir::BinOp::Eq,
        surface::BinOp::Ne => fhir::BinOp::Ne,
        surface::BinOp::Gt => fhir::BinOp::Gt,
        surface::BinOp::Ge => fhir::BinOp::Ge,
        surface::BinOp::Lt => fhir::BinOp::Lt,
        surface::BinOp::Le => fhir::BinOp::Le,
        surface::BinOp::Add => fhir::BinOp::Add,
        surface::BinOp::Sub => fhir::BinOp::Sub,
        surface::BinOp::Mod => fhir::BinOp::Mod,
        surface::BinOp::Mul => fhir::BinOp::Mul,
        surface::BinOp::Div => fhir::BinOp::Div,
    }
}

fn desugar_un_op(op: surface::UnOp) -> fhir::UnOp {
    match op {
        surface::UnOp::Not => fhir::UnOp::Not,
        surface::UnOp::Neg => fhir::UnOp::Neg,
    }
}

impl<'genv> Scope<Param<'genv>> {
    fn to_refine_args<'tcx>(
        &self,
        cx: &impl DesugarCtxt<'genv, 'tcx>,
        span: Span,
    ) -> &'genv [fhir::RefineArg<'genv>]
    where
        'tcx: 'genv,
    {
        cx.genv()
            .alloc_slice_fill_iter(self.iter().map(|(ident, param)| {
                let ident = fhir::Ident::new(param.name, *ident);
                fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(fhir::Expr {
                        kind: ExprKind::Var(ident, None),
                        span,
                        fhir_id: cx.next_fhir_id(),
                    }),
                    fhir_id: cx.next_fhir_id(),
                    span,
                }
            }))
    }

    fn into_params<'tcx>(
        self,
        cx: &impl DesugarCtxt<'genv, 'tcx>,
    ) -> &'genv [fhir::RefineParam<'genv>]
    where
        'tcx: 'genv,
    {
        cx.genv()
            .alloc_slice_fill_iter(self.into_iter().map(|(ident, param)| {
                let ident = fhir::Ident::new(param.name, ident);
                let fhir_id = cx.next_fhir_id();
                fhir::RefineParam {
                    ident,
                    sort: param.sort,
                    kind: param.kind,
                    fhir_id,
                    span: param.span,
                }
            }))
    }
}

trait DesugarCtxt<'genv, 'tcx: 'genv> {
    fn genv(&self) -> GlobalEnv<'genv, 'tcx>;
    fn resolver_output(&self) -> &ResolverOutput;
    fn next_fhir_id(&self) -> FhirId;

    fn sess(&self) -> &'genv FluxSession {
        self.genv().sess()
    }

    fn map(&self) -> global_env::Map<'genv, 'tcx> {
        self.genv().map()
    }

    fn desugar_expr(
        &self,
        env: &mut Env<'genv>,
        expr: &surface::Expr,
    ) -> Result<fhir::Expr<'genv>> {
        let kind = match &expr.kind {
            surface::ExprKind::QPath(qpath) => {
                match self.resolve_qpath(env, qpath)? {
                    QPathRes::Param(ident) => fhir::ExprKind::Var(ident, None),
                    QPathRes::Const(const_def_id) => {
                        fhir::ExprKind::Const(const_def_id, qpath.span)
                    }
                    QPathRes::NumConst(i) => fhir::ExprKind::Literal(fhir::Lit::Int(i)),
                }
            }
            surface::ExprKind::Literal(lit) => {
                fhir::ExprKind::Literal(self.desugar_lit(expr.span, *lit)?)
            }
            surface::ExprKind::BinaryOp(op, box [e1, e2]) => {
                let e1 = self.desugar_expr(env, e1);
                let e2 = self.desugar_expr(env, e2);
                fhir::ExprKind::BinaryOp(
                    desugar_bin_op(*op),
                    self.genv().alloc(e1?),
                    self.genv().alloc(e2?),
                )
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(
                    desugar_un_op(*op),
                    self.genv().alloc(self.desugar_expr(env, e)?),
                )
            }
            surface::ExprKind::Dot(qpath, fld) => {
                if let QPathRes::Param(ident) = self.resolve_qpath(env, qpath)? {
                    fhir::ExprKind::Dot(ident, *fld)
                } else {
                    return Err(self.emit_err(errors::InvalidDotVar { span: expr.span }));
                }
            }
            surface::ExprKind::App(func, args) => {
                let args = self.desugar_exprs(env, args)?;
                match self.resolve_func(env, *func)? {
                    FuncRes::Global(funckind) => {
                        fhir::ExprKind::App(
                            fhir::Func::Global(func.name, funckind, func.span, self.next_fhir_id()),
                            args,
                        )
                    }
                    FuncRes::Param(ident) => {
                        let func = fhir::Func::Var(ident, self.next_fhir_id());
                        fhir::ExprKind::App(func, args)
                    }
                }
            }
            surface::ExprKind::IfThenElse(box [p, e1, e2]) => {
                let p = self.desugar_expr(env, p);
                let e1 = self.desugar_expr(env, e1);
                let e2 = self.desugar_expr(env, e2);
                fhir::ExprKind::IfThenElse(
                    self.genv().alloc(p?),
                    self.genv().alloc(e1?),
                    self.genv().alloc(e2?),
                )
            }
        };

        Ok(fhir::Expr { kind, span: expr.span, fhir_id: self.next_fhir_id() })
    }

    fn desugar_exprs(
        &self,
        env: &mut Env<'genv>,
        exprs: &[surface::Expr],
    ) -> Result<&'genv [fhir::Expr<'genv>]> {
        try_alloc_slice!(self.genv(), exprs, |e| self.desugar_expr(env, e))
    }

    fn try_parse_int_lit(&self, span: Span, s: &str) -> Result<i128> {
        let parsed_int = if s.len() <= 2 {
            s.parse::<i128>()
        } else {
            match &s[0..2] {
                "0x" => i128::from_str_radix(&s[2..], 16), // hex
                "0o" => i128::from_str_radix(&s[2..], 8),  // octal
                "0b" => i128::from_str_radix(&s[2..], 2),  // binary
                _ => s.parse::<i128>(),                    // must be decimal
            }
        };

        if let Ok(n) = parsed_int {
            Ok(n) // convert error types
        } else {
            Err(self.emit_err(errors::IntTooLarge { span }))
        }
    }

    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> Result<fhir::Lit> {
        match lit.kind {
            surface::LitKind::Integer => {
                let n = self.try_parse_int_lit(span, lit.symbol.as_str())?;
                let suffix = lit.suffix.unwrap_or(SORTS.int);
                if suffix == SORTS.int {
                    Ok(fhir::Lit::Int(n))
                } else if suffix == SORTS.real {
                    Ok(fhir::Lit::Real(n))
                } else {
                    Err(self.emit_err(errors::InvalidNumericSuffix::new(span, suffix)))
                }
            }
            surface::LitKind::Bool => Ok(fhir::Lit::Bool(lit.symbol == kw::True)),
            _ => Err(self.emit_err(errors::UnexpectedLiteral { span })),
        }
    }

    fn resolve_func(&self, env: &Env, func: surface::Ident) -> Result<FuncRes> {
        if let Some(param) = env.get(func) {
            return Ok(FuncRes::Param(fhir::Ident::new(param.name, func)));
        }
        if let Some(decl) = self.resolver_output().func_decls.get(&func.name) {
            return Ok(FuncRes::Global(*decl));
        }
        Err(self.emit_err(errors::UnresolvedVar::from_ident(func, "function")))
    }

    fn resolve_qpath(&self, env: &Env, qpath: &surface::QPathExpr) -> Result<QPathRes> {
        match &qpath.segments[..] {
            [var] => {
                if let Some(param) = env.get(*var) {
                    return Ok(QPathRes::Param(fhir::Ident::new(param.name, *var)));
                }
                if let Some(const_def_id) = self.resolver_output().consts.get(&var.name) {
                    return Ok(QPathRes::Const(*const_def_id));
                }
                Err(self.emit_err(errors::UnresolvedVar::from_ident(*var, "name")))
            }
            [typ, name] => {
                resolve_num_const(*typ, *name).ok_or_else(|| {
                    self.emit_err(errors::UnresolvedVar::from_qpath(qpath, "type-2"))
                })
            }
            _ => Err(self.emit_err(errors::UnresolvedVar::from_qpath(qpath, "type-3"))),
        }
    }

    fn resolve_loc(&self, env: &Env, loc: surface::Ident) -> Result<(usize, fhir::Ident)> {
        match env.get(loc) {
            Some(param) => {
                let fhir::ParamKind::Loc(idx) = param.kind else {
                    span_bug!(loc.span, "not a loc");
                };
                Ok((idx, fhir::Ident::new(param.name, loc)))
            }
            None => Err(self.emit_err(errors::UnresolvedVar::from_ident(loc, "location"))),
        }
    }

    #[track_caller]
    fn emit_err(&self, err: impl IntoDiagnostic<'genv>) -> ErrorGuaranteed {
        self.sess().emit_err(err)
    }
}

impl<'a, 'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for RustItemCtxt<'a, 'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &ResolverOutput {
        self.resolver_output
    }
}

impl<'a, 'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for FluxItemCtxt<'a, 'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Flux(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &ResolverOutput {
        self.resolver_output
    }
}

macro_rules! define_resolve_num_const {
    ($($typ:ident),*) => {
        fn resolve_num_const(typ: surface::Ident, name: surface::Ident) -> Option<QPathRes> {
            match typ.name.as_str() {
                $(
                    stringify!($typ) => {
                        match name.name.as_str() {
                            "MAX" => Some(QPathRes::NumConst($typ::MAX.try_into().unwrap())),
                            "MIN" => Some(QPathRes::NumConst($typ::MIN.try_into().unwrap())),
                            _ => None,
                        }
                    },
                )*
                _ => None
            }
        }
    };
}

define_resolve_num_const!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);
