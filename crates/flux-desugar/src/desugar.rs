mod env;
mod gather;
use std::iter;

use flux_common::{bug, index::IndexGen, iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, lift::LiftCtxt, ExprKind, FhirId, FluxOwnerId, Res},
    global_env::GlobalEnv,
};
use flux_syntax::surface;
use hir::{def::DefKind, ItemKind};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::OwnerId;
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
    resolver::ResolverOutput,
    sort_resolver::{SortResolver, SORTS},
};

pub fn desugar_qualifier(
    genv: &GlobalEnv,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier> {
    let sort_params = &[];
    let sort_resolver =
        SortResolver::with_sort_params(genv.sess, genv.map().sort_decls(), sort_params);

    let mut env = Env::from_params(genv, &sort_resolver, ScopeId::FluxItem, &qualifier.args)?;

    let cx = FluxItemCtxt::new(genv, qualifier.name.name);
    let expr = cx.desugar_expr(&mut env, &qualifier.expr);

    Ok(fhir::Qualifier {
        name: qualifier.name.name,
        args: env.into_root().into_params(&cx),
        global: qualifier.global,
        expr: expr?,
    })
}

pub fn desugar_defn(genv: &GlobalEnv, defn: surface::FuncDef) -> Result<Option<fhir::Defn>> {
    if let Some(body) = defn.body {
        let sort_params = defn.sort_vars.iter().map(|ident| ident.name).collect_vec();
        let sort_resolver =
            SortResolver::with_sort_params(genv.sess, genv.map().sort_decls(), &sort_params);
        let mut env = Env::from_params(genv, &sort_resolver, ScopeId::FluxItem, &defn.args)?;

        let cx = FluxItemCtxt::new(genv, defn.name.name);
        let expr = cx.desugar_expr(&mut env, &body)?;
        let name = defn.name.name;
        let params = defn.sort_vars.len();
        let sort = sort_resolver.resolve_sort(&defn.output)?;
        let args = env.into_root().into_params(&cx);

        Ok(Some(fhir::Defn { name, params, args, sort, expr }))
    } else {
        Ok(None)
    }
}

pub fn func_def_to_func_decl(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    defn: &surface::FuncDef,
) -> Result<fhir::FuncDecl> {
    let params = defn.sort_vars.len();
    let sort_vars = defn.sort_vars.iter().map(|ident| ident.name).collect_vec();
    let sr = SortResolver::with_sort_params(sess, sort_decls, &sort_vars);
    let inputs: Vec<fhir::Sort> = defn
        .args
        .iter()
        .map(|arg| sr.resolve_sort(&arg.sort))
        .try_collect_exhaust()?;
    let output = sr.resolve_sort(&defn.output)?;
    let sort = fhir::PolyFuncSort::new(params, inputs, output);
    let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
    Ok(fhir::FuncDecl { name: defn.name.name, sort, kind })
}

fn gather_base_sort_vars(
    generics: &FxHashSet<Symbol>,
    base_sort: &surface::BaseSort,
    sort_vars: &mut FxHashSet<Symbol>,
) {
    match base_sort {
        surface::BaseSort::Ident(x) => {
            if generics.contains(&x.name) {
                sort_vars.insert(x.name);
            }
        }
        surface::BaseSort::BitVec(_) => {}
        surface::BaseSort::App(_, base_sorts) => {
            for base_sort in base_sorts {
                gather_base_sort_vars(generics, base_sort, sort_vars);
            }
        }
    }
}

fn gather_sort_vars(
    generics: &FxHashSet<Symbol>,
    sort: &surface::Sort,
    sort_vars: &mut FxHashSet<Symbol>,
) {
    match sort {
        surface::Sort::Base(base_sort) => gather_base_sort_vars(generics, base_sort, sort_vars),
        surface::Sort::Func { inputs, output } => {
            for base_sort in inputs {
                gather_base_sort_vars(generics, base_sort, sort_vars);
            }
            gather_base_sort_vars(generics, output, sort_vars);
        }
        surface::Sort::Infer => {}
    }
}

fn gather_refined_by_sort_vars(
    generics: &rustc_middle::ty::Generics,
    refined_by: &surface::RefinedBy,
) -> Vec<Symbol> {
    let generics_syms: FxHashSet<Symbol> = generics.params.iter().map(|param| param.name).collect();
    let mut sort_idents = FxHashSet::default();
    for refine_param in &refined_by.index_params {
        gather_sort_vars(&generics_syms, &refine_param.sort, &mut sort_idents);
    }
    generics
        .params
        .iter()
        .filter_map(|param| if sort_idents.contains(&param.name) { Some(param.name) } else { None })
        .collect()
}

pub fn desugar_refined_by(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    owner_id: OwnerId,
    generics: &rustc_middle::ty::Generics,
    refined_by: &surface::RefinedBy,
) -> Result<fhir::RefinedBy> {
    let mut set = FxHashSet::default();
    refined_by.all_params().try_for_each_exhaust(|param| {
        if let Some(old) = set.replace(param.name) {
            Err(sess.emit_err(errors::DuplicateParam::new(old, param.name)))
        } else {
            Ok(())
        }
    })?;

    let sort_vars = gather_refined_by_sort_vars(generics, refined_by);
    let sr = SortResolver::with_sort_params(sess, sort_decls, &sort_vars);

    let early_bound_params: Vec<_> = refined_by
        .early_bound_params
        .iter()
        .map(|param| sr.resolve_sort(&param.sort))
        .try_collect_exhaust()?;

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

    Ok(fhir::RefinedBy::new(
        owner_id.def_id,
        early_bound_params,
        index_params,
        sort_params,
        refined_by.span,
    ))
}

pub(crate) struct RustItemCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
    resolver_output: &'a ResolverOutput,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
    sort_resolver: SortResolver<'a>,
}

type Env = env::Env<Param>;

#[derive(Debug, Clone)]
struct Param {
    name: fhir::Name,
    sort: fhir::Sort,
    kind: fhir::ParamKind,
}

struct FluxItemCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: Symbol,
}

enum FuncRes<'a> {
    Param(fhir::Ident),
    Global(&'a fhir::FuncDecl),
}

enum QPathRes<'a> {
    Param(fhir::Ident),
    Const(&'a fhir::ConstInfo),
    NumConst(i128),
}

fn super_hack_is_impl(def_id: DefId) -> bool {
    format!("{def_id:?}").contains("::{impl#")
}

fn self_sort(genv: &GlobalEnv, parent_id: Option<DefId>) -> Option<fhir::Sort> {
    if let Some(alias_to) = parent_id
        && super_hack_is_impl(alias_to)
    {
        genv.sort_of_self_ty_alias(alias_to)
    } else {
        None
    }
}

impl<'a, 'tcx> RustItemCtxt<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        owner: OwnerId,
        resolver_output: &'a ResolverOutput,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
    ) -> RustItemCtxt<'a, 'tcx> {
        let generics = genv.tcx.generics_of(owner);

        let owner_id = owner.def_id.to_def_id();
        let parent_id = genv.tcx.opt_parent(owner_id);
        let self_sort = self_sort(genv, parent_id);
        let sort_resolver = SortResolver::with_generics(
            genv.sess,
            genv.map().sort_decls(),
            generics,
            parent_id,
            self_sort,
        );
        RustItemCtxt {
            genv,
            owner,
            local_id_gen: IndexGen::new(),
            sort_resolver,
            resolver_output,
            opaque_tys,
        }
    }

    fn with_new_owner<'b>(&'b mut self, owner: OwnerId) -> RustItemCtxt<'b, 'tcx> {
        RustItemCtxt::new(self.genv, owner, self.resolver_output, self.opaque_tys.as_deref_mut())
    }

    pub(crate) fn as_lift_cx<'b>(&'b mut self) -> LiftCtxt<'b, 'tcx> {
        LiftCtxt::new(self.genv.tcx, self.genv.sess, self.owner, self.opaque_tys.as_deref_mut())
    }

    /// [desugar_generics] starts with the `lifted_generics` and "updates" it with the surface `generics`
    pub(crate) fn desugar_generics(
        &self,
        lifted_generics: fhir::Generics,
        generics: &surface::Generics,
    ) -> Result<fhir::Generics> {
        let generics = self.desugar_generics_inner(generics)?;
        self.with_desugared_generics(lifted_generics, generics)
    }

    pub(crate) fn with_desugared_generics(
        &self,
        lifted_generics: fhir::Generics,
        generics: fhir::Generics,
    ) -> Result<fhir::Generics> {
        let generics_map: FxHashMap<_, _> = generics
            .params
            .into_iter()
            .map(|param| (param.def_id, param.kind))
            .collect();

        let params = lifted_generics
            .params
            .iter()
            .map(|lifted_param| {
                let def_id = lifted_param.def_id;
                let kind = generics_map.get(&def_id).unwrap_or(&lifted_param.kind);
                fhir::GenericParam { def_id, kind: kind.clone() }
            })
            .collect();

        Ok(fhir::Generics { params, self_kind: generics.self_kind.clone() })
    }

    fn desugar_generics_inner(&self, generics: &surface::Generics) -> Result<fhir::Generics> {
        let hir_generics = self.genv.hir().get_generics(self.owner.def_id).unwrap();
        let generics_map: FxHashMap<_, _> = hir_generics
            .params
            .iter()
            .flat_map(|param| {
                if let hir::ParamName::Plain(name) = param.name {
                    Some((name, param.def_id))
                } else {
                    None
                }
            })
            .collect();

        let mut params = vec![];
        let mut self_kind = None;
        for param in &generics.params {
            let kind = match &param.kind {
                surface::GenericParamKind::Type => fhir::GenericParamKind::Type { default: None },
                surface::GenericParamKind::Base => fhir::GenericParamKind::BaseTy,
                surface::GenericParamKind::Spl => fhir::GenericParamKind::SplTy,
                surface::GenericParamKind::Refine { .. } => {
                    continue;
                }
            };

            if &param.name.name == &kw::SelfUpper {
                self_kind = Some(kind);
            } else {
                let def_id = *generics_map.get(&param.name).ok_or_else(|| {
                    self.emit_err(errors::UnresolvedGenericParam::new(param.name))
                })?;
                params.push(fhir::GenericParam { def_id, kind });
            }
        }
        Ok(fhir::Generics { params, self_kind })
    }

    fn desugar_predicates(
        &mut self,
        predicates: &Vec<surface::WhereBoundPredicate>,
        env: &mut Env,
    ) -> Result<fhir::GenericPredicates> {
        let mut res = vec![];
        for pred in predicates {
            res.push(self.desugar_predicate(pred, env)?);
        }
        Ok(fhir::GenericPredicates { predicates: res })
    }

    fn desugar_predicate(
        &mut self,
        pred: &surface::WhereBoundPredicate,
        env: &mut Env,
    ) -> Result<fhir::WhereBoundPredicate> {
        let bounded_ty = self.desugar_ty(None, &pred.bounded_ty, env)?;
        let bounds = self.desugar_generic_bounds(&pred.bounds, env)?;
        Ok(fhir::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
    }

    fn desugar_generic_bounds(
        &mut self,
        bounds: &surface::GenericBounds,
        env: &mut Env,
    ) -> Result<fhir::GenericBounds> {
        bounds
            .iter()
            .map(|bound| {
                Ok(fhir::GenericBound::Trait(
                    self.desugar_trait_ref(bound, env)?,
                    fhir::TraitBoundModifier::None,
                ))
            })
            .try_collect_exhaust()
    }

    fn desugar_trait_ref(
        &mut self,
        trait_ref: &surface::TraitRef,
        env: &mut Env,
    ) -> Result<fhir::PolyTraitRef> {
        Ok(fhir::PolyTraitRef {
            bound_generic_params: vec![],
            trait_ref: self.desugar_path(&trait_ref.path, env)?,
        })
    }

    pub(crate) fn desugar_struct_def(
        &mut self,
        struct_def: &surface::StructDef,
    ) -> Result<fhir::StructDef> {
        let mut env = self.gather_params_struct(struct_def)?;

        let invariants = struct_def
            .invariants
            .iter()
            .map(|invariant| self.desugar_expr(&mut env, invariant))
            .try_collect_exhaust()?;

        let kind = if struct_def.opaque {
            fhir::StructKind::Opaque
        } else {
            let hir::ItemKind::Struct(variant_data, _) =
                &self.genv.hir().expect_item(self.owner.def_id).kind
            else {
                bug!("expected struct")
            };
            debug_assert_eq!(struct_def.fields.len(), variant_data.fields().len());
            let fields = iter::zip(&struct_def.fields, variant_data.fields())
                .map(|(ty, hir_field)| {
                    if let Some(ty) = ty {
                        Ok(fhir::FieldDef {
                            ty: self.desugar_ty(None, ty, &mut env)?,
                            def_id: hir_field.def_id,
                            lifted: false,
                        })
                    } else {
                        self.as_lift_cx().lift_field_def(hir_field)
                    }
                })
                .try_collect_exhaust()?;
            fhir::StructKind::Transparent { fields }
        };
        Ok(fhir::StructDef {
            owner_id: self.owner,
            params: env.into_root().into_params(self),
            kind,
            invariants,
        })
    }

    pub(crate) fn desugar_enum_def(
        &mut self,
        enum_def: &surface::EnumDef,
    ) -> Result<fhir::EnumDef> {
        let def_id = self.owner.def_id;
        let ItemKind::Enum(hir_enum, _) = &self.genv.hir().expect_item(def_id).kind else {
            bug!("expected enum");
        };
        let variants = iter::zip(&enum_def.variants, hir_enum.variants)
            .map(|(variant, hir_variant)| self.desugar_enum_variant_def(variant, hir_variant))
            .try_collect_exhaust()?;

        let mut env = Env::from_params(
            self.genv,
            &self.sort_resolver,
            ScopeId::Enum(enum_def.node_id),
            enum_def
                .refined_by
                .iter()
                .flat_map(surface::RefinedBy::all_params),
        )?;

        let invariants = enum_def
            .invariants
            .iter()
            .map(|invariant| self.desugar_expr(&mut env, invariant))
            .try_collect_exhaust()?;

        Ok(fhir::EnumDef {
            owner_id: self.owner,
            params: env.into_root().into_params(self),
            variants,
            invariants,
            extern_id: enum_def.extern_id,
        })
    }

    fn desugar_enum_variant_def(
        &mut self,
        variant_def: &Option<surface::VariantDef>,
        hir_variant: &hir::Variant,
    ) -> Result<fhir::VariantDef> {
        if let Some(variant_def) = variant_def {
            let mut env = self.gather_params_variant(variant_def)?;

            let fields = iter::zip(&variant_def.fields, hir_variant.data.fields())
                .map(|(ty, hir_field)| {
                    Ok(fhir::FieldDef {
                        ty: self.desugar_ty(None, ty, &mut env)?,
                        def_id: hir_field.def_id,
                        lifted: false,
                    })
                })
                .try_collect_exhaust()?;

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

    pub(crate) fn desugar_type_alias(
        &mut self,
        ty_alias: &surface::TyAlias,
    ) -> Result<fhir::TyAlias> {
        let mut env = self.gather_params_type_alias(ty_alias)?;

        let ty = self.desugar_ty(None, &ty_alias.ty, &mut env)?;

        let mut early_bound_params = env.into_root().into_params(self);
        let index_params =
            early_bound_params.split_off(ty_alias.refined_by.early_bound_params.len());

        Ok(fhir::TyAlias {
            owner_id: self.owner,
            early_bound_params,
            index_params,
            ty,
            span: ty_alias.span,
            lifted: false,
        })
    }

    pub(crate) fn desugar_fn_sig(
        &mut self,
        fn_sig: &surface::FnSig,
    ) -> Result<(fhir::GenericPredicates, fhir::FnSig)> {
        let mut env = self.gather_params_fn_sig(fn_sig)?;

        let mut requires = vec![];

        // Desugar predicates -- after we have gathered the input params
        let generic_preds = if let Some(predicates) = &fn_sig.predicates {
            self.desugar_predicates(predicates, &mut env)?
        } else {
            self.as_lift_cx().lift_predicates()?
        };

        if let Some(e) = &fn_sig.requires {
            let pred = self.desugar_expr(&mut env, e)?;
            requires.push(fhir::Constraint::Pred(pred));
        }

        // Bail out if there's an error in the arguments to avoid confusing error messages
        let args = fn_sig
            .args
            .iter()
            .map(|arg| self.desugar_fun_arg(arg, &mut env, &mut requires))
            .try_collect_exhaust()?;

        // Desugar output
        env.enter(ScopeId::FnOutput(fn_sig.node_id));
        let ret = self.desugar_asyncness(fn_sig.asyncness, &fn_sig.returns, &mut env);

        let ensures = fn_sig
            .ensures
            .iter()
            .map(|cstr| self.desugar_constraint(cstr, &mut env))
            .try_collect_exhaust()?;

        let output = fhir::FnOutput { params: env.pop().into_params(self), ret: ret?, ensures };

        let fn_sig = fhir::FnSig {
            params: env.into_root().into_params(self),
            requires,
            args,
            output,
            span: fn_sig.span,
            lifted: false,
        };
        Ok((generic_preds, fn_sig))
    }

    fn desugar_constraint(
        &mut self,
        cstr: &surface::Constraint,
        env: &mut Env,
    ) -> Result<fhir::Constraint> {
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
        env: &mut Env,
        requires: &mut Vec<fhir::Constraint>,
    ) -> Result<fhir::Ty> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let bty = self.desugar_path_to_bty(path, env)?;

                let pred = self.desugar_expr(env, pred)?;

                let sort = self.genv.sort_of_bty(&bty);
                let ty = if let Some(idx) = self.bind_into_refine_arg(*bind, sort, env)? {
                    fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: path.span }
                } else {
                    fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: path.span }
                };

                let span = path.span.to(pred.span);
                let kind = fhir::TyKind::Constr(pred, Box::new(ty));
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
        env: &mut Env,
    ) -> Result<fhir::Ty> {
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
        env: &mut Env,
    ) -> Result<fhir::OpaqueTy> {
        let output = self.desugar_fn_ret_ty(returns, env)?;
        let bound = fhir::GenericBound::LangItemTrait(
            hir::LangItem::Future,
            vec![],
            vec![fhir::TypeBinding {
                ident: surface::Ident::with_dummy_span(sym::Output),
                term: output,
            }],
        );
        Ok(fhir::OpaqueTy { bounds: vec![bound] })
    }

    fn desugar_fn_ret_ty(&mut self, returns: &surface::FnRetTy, env: &mut Env) -> Result<fhir::Ty> {
        match returns {
            surface::FnRetTy::Ty(ty) => self.desugar_ty(None, ty, env),
            surface::FnRetTy::Default(span) => {
                let kind = fhir::TyKind::Tuple(vec![]);
                Ok(fhir::Ty { kind, span: *span })
            }
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        env: &mut Env,
    ) -> Result<fhir::Ty> {
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
                let idx = self.desugar_indices(&bty, indices, env)?;
                fhir::TyKind::Indexed(bty, idx)
            }
            surface::TyKind::Exists { bind: ex_bind, bty, pred } => {
                let ty_span = ty.span;
                let bty_span = bty.span;

                env.enter(ScopeId::Exists(node_id));

                let bty = self.desugar_bty(bty, env)?;

                if let Some(sort) = self.genv.sort_of_bty(&bty) {
                    env.get_mut(*ex_bind).unwrap().sort = sort;
                } else {
                    return Err(self.emit_err(errors::RefinedUnrefinableType::new(bty.span)));
                };

                let pred = self.desugar_expr(env, pred)?;
                let params = env.pop().into_params(self);

                let idx = fhir::RefineArg::Expr {
                    expr: fhir::Expr {
                        kind: fhir::ExprKind::Var(params[0].ident),
                        span: ex_bind.span,
                        fhir_id: self.next_fhir_id(),
                    },
                    is_binder: false,
                };
                let indexed = fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: bty_span };
                let constr =
                    fhir::Ty { kind: fhir::TyKind::Constr(pred, Box::new(indexed)), span: ty_span };
                fhir::TyKind::Exists(params, Box::new(constr))
            }
            surface::TyKind::GeneralExists { ty, pred, .. } => {
                env.enter(ScopeId::Exists(node_id));
                let mut ty = self.desugar_ty(None, ty, env)?;
                if let Some(pred) = pred {
                    let pred = self.desugar_expr(env, pred)?;
                    let span = ty.span.to(pred.span);
                    ty = fhir::Ty { kind: fhir::TyKind::Constr(pred, Box::new(ty)), span };
                }
                let params = env.pop().into_params(self);

                fhir::TyKind::Exists(params, Box::new(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.desugar_expr(env, pred)?;
                let ty = self.desugar_ty(None, ty, env)?;
                fhir::TyKind::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let mut_ty =
                    fhir::MutTy { ty: Box::new(self.desugar_ty(None, ty, env)?), mutbl: *mutbl };
                fhir::TyKind::Ref(self.mk_lft_hole(), mut_ty)
            }
            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.desugar_ty(None, ty, env))
                    .try_collect_exhaust()?;
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(None, ty, env)?;
                fhir::TyKind::Array(Box::new(ty), fhir::ArrayLen { val: len.val, span: len.span })
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
        env: &mut Env,
    ) -> Result<fhir::OpaqueTy> {
        let bounds = self.desugar_generic_bounds(bounds, env)?;
        Ok(fhir::OpaqueTy { bounds })
    }

    fn mk_lft_hole(&self) -> fhir::Lifetime {
        fhir::Lifetime::Hole(self.next_fhir_id())
    }

    fn desugar_indices(
        &mut self,
        bty: &fhir::BaseTy,
        idxs: &surface::Indices,
        env: &mut Env,
    ) -> Result<fhir::RefineArg> {
        let Some(sort) = self.genv.sort_of_bty(bty) else {
            return Err(self.emit_err(errors::RefinedUnrefinableType::new(bty.span)));
        };
        if let fhir::Sort::Record(def_id, sort_args) = sort.clone() {
            if let [surface::RefineArg::Bind(ident, ..)] = &idxs.indices[..] {
                Ok(self.bind_into_refine_arg(*ident, Some(sort), env)?.unwrap())
            } else {
                let sorts = self.genv.index_sorts_of(def_id, &sort_args);
                if sorts.len() != idxs.indices.len() {
                    return Err(
                        self.emit_err(errors::RefineArgCountMismatch::new(idxs, sorts.len()))
                    );
                }
                let flds = iter::zip(&idxs.indices, sorts)
                    .map(|(arg, sort)| self.desugar_refine_arg(arg, Some(sort), env))
                    .try_collect_exhaust()?;
                Ok(fhir::RefineArg::Record(def_id, sort_args, flds, idxs.span))
            }
        } else if let [arg] = &idxs.indices[..] {
            self.desugar_refine_arg(arg, Some(sort), env)
        } else {
            Err(self.emit_err(errors::RefineArgCountMismatch::new(idxs, 1)))
        }
    }

    fn desugar_refine_arg(
        &mut self,
        arg: &surface::RefineArg,
        sort: Option<fhir::Sort>,
        env: &mut Env,
    ) -> Result<fhir::RefineArg> {
        match arg {
            surface::RefineArg::Bind(ident, ..) => {
                Ok(self.bind_into_refine_arg(*ident, sort, env)?.unwrap())
            }
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg::Expr { expr: self.desugar_expr(env, expr)?, is_binder: false })
            }
            surface::RefineArg::Abs(_, body, node_id, span) => {
                env.enter(ScopeId::Abs(*node_id));
                let body = self.desugar_expr(env, body)?;
                let params = env.pop().into_params(self);
                Ok(fhir::RefineArg::Abs(params, body, *span, self.next_fhir_id()))
            }
        }
    }

    fn bind_into_refine_arg(
        &self,
        ident: surface::Ident,
        sort: Option<fhir::Sort>,
        env: &mut Env,
    ) -> Result<Option<fhir::RefineArg>> {
        match env.get_mut(ident) {
            Some(param) => {
                if let Some(sort) = sort {
                    param.sort = sort;
                } else {
                    param.sort = fhir::Sort::Error;
                }
                let kind = fhir::ExprKind::Var(fhir::Ident::new(param.name, ident));
                let expr = fhir::Expr { kind, span: ident.span, fhir_id: self.next_fhir_id() };
                Ok(Some(fhir::RefineArg::Expr { expr, is_binder: true }))
            }
            None => Ok(None),
        }
    }

    fn desugar_bty(&mut self, bty: &surface::BaseTy, env: &mut Env) -> Result<fhir::BaseTy> {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.desugar_path_to_bty(path, env),
            surface::BaseTyKind::Slice(ty) => {
                let kind = fhir::BaseTyKind::Slice(Box::new(self.desugar_ty(None, ty, env)?));
                Ok(fhir::BaseTy { kind, span: bty.span })
            }
        }
    }

    fn desugar_path(&mut self, path: &surface::Path, env: &mut Env) -> Result<fhir::Path> {
        let res = self.resolver_output.path_res_map[&path.node_id];
        let (args, bindings) = self.desugar_generic_args(res, &path.generics, env)?;
        let refine = path
            .refine
            .iter()
            .map(|arg| self.desugar_refine_arg(arg, None, env))
            .try_collect_exhaust()?;
        Ok(fhir::Path { res, args, bindings, refine, span: path.span })
    }

    fn desugar_path_to_bty(&mut self, path: &surface::Path, env: &mut Env) -> Result<fhir::BaseTy> {
        Ok(fhir::BaseTy::from(fhir::QPath::Resolved(None, self.desugar_path(path, env)?)))
    }

    fn desugar_generic_args(
        &mut self,
        res: Res,
        args: &[surface::GenericArg],
        env: &mut Env,
    ) -> Result<(Vec<fhir::GenericArg>, Vec<fhir::TypeBinding>)> {
        let mut fhir_args = vec![];
        let mut bindings = vec![];
        if let Res::Def(
            DefKind::TyAlias { .. } | DefKind::Struct | DefKind::Enum | DefKind::OpaqueTy,
            def_id,
        ) = res
        {
            let generics = self.genv.tcx.generics_of(def_id);
            for param in &generics.params {
                if let rustc_middle::ty::GenericParamDefKind::Lifetime = param.kind {
                    fhir_args.push(fhir::GenericArg::Lifetime(self.mk_lft_hole()));
                }
            }
        }
        for arg in args {
            match arg {
                surface::GenericArg::Type(ty) => {
                    fhir_args.push(fhir::GenericArg::Type(self.desugar_ty(None, ty, env)?));
                }
                surface::GenericArg::Constraint(ident, ty) => {
                    bindings.push(fhir::TypeBinding {
                        ident: *ident,
                        term: self.desugar_ty(None, ty, env)?,
                    });
                }
            }
        }
        Ok((fhir_args, bindings))
    }

    fn desugar_bty_bind(
        &mut self,
        bind: Option<surface::Ident>,
        bty: &surface::BaseTy,
        env: &mut Env,
    ) -> Result<fhir::Ty> {
        let bty = self.desugar_bty(bty, env)?;

        let span = bty.span;
        let kind = if let Some(bind) = bind
            && let sort = self.genv.sort_of_bty(&bty)
            && let Some(idx) = self.bind_into_refine_arg(bind, sort, env)?
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
        env: &mut Env,
    ) -> Result<fhir::VariantRet> {
        let bty = self.desugar_path_to_bty(&ret.path, env)?;
        let idx = self.desugar_indices(&bty, &ret.indices, env)?;
        Ok(fhir::VariantRet { bty, idx })
    }

    fn insert_opaque_ty(&mut self, def_id: LocalDefId, opaque_ty: fhir::OpaqueTy) {
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item {def_id:?}"))
            .insert(def_id, opaque_ty);
    }

    fn sess(&self) -> &'a FluxSession {
        self.genv.sess
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.sess().emit_err(err)
    }
}

impl<'a, 'tcx> FluxItemCtxt<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>, owner: Symbol) -> Self {
        Self { genv, local_id_gen: Default::default(), owner }
    }
}

impl Env {
    fn from_params<'a>(
        genv: &GlobalEnv,
        sort_resolver: &SortResolver,
        scope: ScopeId,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<Self> {
        let mut env = Env::new(scope);
        let name_gen = IndexGen::new();
        for param in params {
            let sort = sort_resolver.resolve_sort(&param.sort)?;
            env.insert(
                genv.sess,
                param.name,
                Param { name: name_gen.fresh(), sort, kind: fhir::ParamKind::Explicit },
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

impl Scope<Param> {
    fn to_refine_args<'a, 'tcx: 'a>(
        &self,
        cx: &impl DesugarCtxt<'a, 'tcx>,
        span: Span,
    ) -> Vec<fhir::RefineArg> {
        let mut refine_args = vec![];
        for (ident, param) in self.iter() {
            let ident = fhir::Ident::new(param.name, *ident);
            let kind = ExprKind::Var(ident);
            let fhir_id = cx.next_fhir_id();
            let expr = fhir::Expr { kind, span, fhir_id };
            refine_args.push(fhir::RefineArg::Expr { expr, is_binder: false });
        }
        refine_args
    }

    fn into_params<'a, 'tcx: 'a>(self, cx: &impl DesugarCtxt<'a, 'tcx>) -> Vec<fhir::RefineParam> {
        let mut params = vec![];
        for (ident, param) in self.into_iter() {
            let ident = fhir::Ident::new(param.name, ident);
            let fhir_id = cx.next_fhir_id();
            params.push(fhir::RefineParam { ident, sort: param.sort, kind: param.kind, fhir_id });
        }
        params
    }
}

trait DesugarCtxt<'a, 'tcx: 'a> {
    fn genv(&self) -> &'a GlobalEnv<'a, 'tcx>;
    fn next_fhir_id(&self) -> FhirId;

    fn desugar_expr(&self, env: &mut Env, expr: &surface::Expr) -> Result<fhir::Expr> {
        let kind = match &expr.kind {
            surface::ExprKind::QPath(qpath) => {
                match self.resolve_qpath(env, qpath)? {
                    QPathRes::Param(ident) => fhir::ExprKind::Var(ident),
                    QPathRes::Const(const_info) => {
                        fhir::ExprKind::Const(const_info.def_id, qpath.span)
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
                fhir::ExprKind::BinaryOp(desugar_bin_op(*op), Box::new([e1?, e2?]))
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(desugar_un_op(*op), Box::new(self.desugar_expr(env, e)?))
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
                    FuncRes::Global(fundecl) => {
                        fhir::ExprKind::App(
                            fhir::Func::Global(
                                func.name,
                                fundecl.kind,
                                func.span,
                                self.next_fhir_id(),
                            ),
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
                fhir::ExprKind::IfThenElse(Box::new([p?, e1?, e2?]))
            }
        };
        Ok(fhir::Expr { kind, span: expr.span, fhir_id: self.next_fhir_id() })
    }

    fn desugar_exprs(&self, env: &mut Env, exprs: &[surface::Expr]) -> Result<Vec<fhir::Expr>> {
        exprs
            .iter()
            .map(|e| self.desugar_expr(env, e))
            .try_collect_exhaust()
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

    fn resolve_func(&self, env: &Env, func: surface::Ident) -> Result<FuncRes<'a>> {
        if let Some(param) = env.get(func) {
            return Ok(FuncRes::Param(fhir::Ident::new(param.name, func)));
        }
        if let Some(decl) = self.genv().func_decl(func.name) {
            return Ok(FuncRes::Global(decl));
        }
        Err(self.emit_err(errors::UnresolvedVar::from_ident(func)))
    }

    fn resolve_qpath(&self, env: &Env, qpath: &surface::QPathExpr) -> Result<QPathRes<'a>> {
        match &qpath.segments[..] {
            [var] => {
                if let Some(param) = env.get(*var) {
                    return Ok(QPathRes::Param(fhir::Ident::new(param.name, *var)));
                }
                if let Some(const_info) = self.genv().const_by_name(var.name) {
                    return Ok(QPathRes::Const(const_info));
                }
                Err(self.emit_err(errors::UnresolvedVar::from_ident(*var)))
            }
            [typ, name] => {
                resolve_num_const(*typ, *name)
                    .ok_or_else(|| self.emit_err(errors::UnresolvedVar::from_qpath(qpath)))
            }
            _ => Err(self.emit_err(errors::UnresolvedVar::from_qpath(qpath))),
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
            None => Err(self.emit_err(errors::UnresolvedVar::from_ident(loc))),
        }
    }

    #[track_caller]
    fn emit_err(&self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        self.genv().sess.emit_err(err)
    }
}

impl<'a, 'tcx> DesugarCtxt<'a, 'tcx> for RustItemCtxt<'a, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn genv(&self) -> &'a GlobalEnv<'a, 'tcx> {
        self.genv
    }
}

impl<'a, 'tcx> DesugarCtxt<'a, 'tcx> for FluxItemCtxt<'a, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Flux(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn genv(&self) -> &'a GlobalEnv<'a, 'tcx> {
        self.genv
    }
}

macro_rules! define_resolve_num_const {
    ($($typ:ident),*) => {
        fn resolve_num_const(typ: surface::Ident, name: surface::Ident) -> Option<QPathRes<'static>> {
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
