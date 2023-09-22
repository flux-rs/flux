use std::{borrow::Borrow, iter, slice};

use flux_common::{bug, index::IndexGen, iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, lift::LiftCtxt, ExprKind, FhirId, FluxOwnerId, Res},
    global_env::GlobalEnv,
    intern::List,
};
use flux_syntax::surface;
use hir::{def::DefKind, ItemKind};
use rustc_data_structures::{
    fx::{FxIndexMap, IndexEntry},
    unord::UnordMap,
};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::OwnerId;
use rustc_span::{
    def_id::LocalDefId,
    sym::{self},
    symbol::kw,
    Span, Symbol,
};

use crate::resolver::ResolverOutput;

pub fn desugar_qualifier(
    genv: &GlobalEnv,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier, ErrorGuaranteed> {
    let mut binders = Binders::from_params(genv, &qualifier.args)?;
    let index_gen = IndexGen::new();
    let cx = ExprCtxt::new(genv, FluxOwnerId::Flux(qualifier.name.name), &index_gen);
    let expr = cx.desugar_expr(&binders, &qualifier.expr);

    Ok(fhir::Qualifier {
        name: qualifier.name.name,
        args: binders.pop_layer().into_params(&cx),
        global: qualifier.global,
        expr: expr?,
    })
}

pub fn desugar_defn(
    genv: &GlobalEnv,
    defn: surface::FuncDef,
) -> Result<Option<fhir::Defn>, ErrorGuaranteed> {
    if let Some(body) = defn.body {
        let mut binders = Binders::from_params(genv, &defn.args)?;
        let local_id_gen = IndexGen::new();
        let cx = ExprCtxt::new(genv, FluxOwnerId::Flux(defn.name.name), &local_id_gen);
        let expr = cx.desugar_expr(&binders, &body)?;
        let name = defn.name.name;
        let sort = resolve_sort(genv.sess, genv.map().sort_decls(), &defn.output)?;
        let args = binders.pop_layer().into_params(&cx);
        Ok(Some(fhir::Defn { name, args, sort, expr }))
    } else {
        Ok(None)
    }
}

pub fn func_def_to_func_decl(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    defn: &surface::FuncDef,
) -> Result<fhir::FuncDecl, ErrorGuaranteed> {
    let mut inputs_and_output: Vec<fhir::Sort> = defn
        .args
        .iter()
        .map(|arg| resolve_sort(sess, sort_decls, &arg.sort))
        .try_collect_exhaust()?;
    inputs_and_output.push(resolve_sort(sess, sort_decls, &defn.output)?);
    let sort = fhir::FuncSort { inputs_and_output: List::from(inputs_and_output) };
    let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
    Ok(fhir::FuncDecl { name: defn.name.name, sort, kind })
}

pub fn desugar_refined_by(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    owner_id: OwnerId,
    refined_by: &surface::RefinedBy,
) -> Result<fhir::RefinedBy, ErrorGuaranteed> {
    let mut set = FxHashSet::default();
    refined_by.all_params().try_for_each_exhaust(|param| {
        if let Some(old) = set.replace(param.name) {
            Err(sess.emit_err(errors::DuplicateParam::new(old, param.name)))
        } else {
            Ok(())
        }
    })?;
    let early_bound_params: Vec<_> = refined_by
        .early_bound_params
        .iter()
        .map(|param| resolve_sort(sess, sort_decls, &param.sort))
        .try_collect_exhaust()?;

    let index_params: Vec<_> = refined_by
        .index_params
        .iter()
        .map(|param| Ok((param.name.name, resolve_sort(sess, sort_decls, &param.sort)?)))
        .try_collect_exhaust()?;

    Ok(fhir::RefinedBy::new(owner_id.def_id, early_bound_params, index_params, refined_by.span))
}

pub(crate) struct DesugarCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
    resolver_output: &'a ResolverOutput,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
}

/// Keeps track of the surface level identifiers in scope and a mapping between them and a
/// [`Binder`].
pub(crate) struct Binders {
    name_gen: IndexGen<fhir::Name>,
    layers: Vec<Layer>,
}

#[derive(Default, Debug)]
struct Layer {
    map: FxIndexMap<surface::Ident, Binder>,
}

/// The different kind of binders that can appear in the surface syntax
#[derive(Debug, Clone)]
pub(crate) enum Binder {
    /// A normal binder to a refinable type that will be desugared as an explicit parameter.
    /// The boolean indicates whether the binder was declared _implicitly_ with the `@` or `#`
    /// syntax.
    ///
    /// [inference mode]: fhir::InferMode
    Refined(fhir::Name, fhir::Sort, /*implicit*/ bool),
    /// A binder to an unrefinable type (a type that cannot be refined). We try to catch this
    /// situation "eagerly" as it will often result in better error messages, e.g., we will
    /// fail if a type parameter `T` of kind `typ` (which cannot be refined) is used as an indexed
    /// type `T[@a]` or as an existential `T{v : v > 0}`, but unrefined binders can appear when
    /// using argument syntax (`x: T`), thus we track them and report appropriate errors if
    /// they are used in any way.
    Unrefined,
}

struct ExprCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
    owner: FluxOwnerId,
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

impl<'a, 'tcx> DesugarCtxt<'a, 'tcx> {
    pub(crate) fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        owner: OwnerId,
        resolver_output: &'a ResolverOutput,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
    ) -> DesugarCtxt<'a, 'tcx> {
        DesugarCtxt { genv, owner, local_id_gen: IndexGen::new(), resolver_output, opaque_tys }
    }

    fn with_new_owner<'b>(&'b mut self, owner: OwnerId) -> DesugarCtxt<'b, 'tcx> {
        DesugarCtxt::new(self.genv, owner, self.resolver_output, self.opaque_tys.as_deref_mut())
    }

    pub(crate) fn as_lift_cx<'b>(&'b mut self) -> LiftCtxt<'b, 'tcx> {
        LiftCtxt::new(
            self.genv.tcx,
            self.genv.sess,
            self.owner,
            &self.local_id_gen,
            self.opaque_tys.as_deref_mut(),
        )
    }

    fn as_expr_ctxt<'b>(&'b self) -> ExprCtxt<'b, 'tcx> {
        ExprCtxt::new(self.genv, FluxOwnerId::Rust(self.owner), &self.local_id_gen)
    }

    pub(crate) fn desugar_generics(
        &self,
        generics: &surface::Generics,
    ) -> Result<fhir::Generics, ErrorGuaranteed> {
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
        for param in &generics.params {
            let kind = match &param.kind {
                surface::GenericParamKind::Type => fhir::GenericParamKind::Type { default: None },
                surface::GenericParamKind::Base => fhir::GenericParamKind::BaseTy,
                surface::GenericParamKind::Refine { .. } => {
                    continue;
                }
            };

            let def_id = *generics_map
                .get(&param.name)
                .ok_or_else(|| self.emit_err(errors::UnresolvedGenericParam::new(param.name)))?;

            params.push(fhir::GenericParam { def_id, kind });
        }
        Ok(fhir::Generics { params })
    }

    fn desugar_predicates(
        &mut self,
        predicates: &Vec<surface::WhereBoundPredicate>,
        binders: &mut Binders,
    ) -> Result<fhir::GenericPredicates, ErrorGuaranteed> {
        let mut res = vec![];
        for pred in predicates {
            res.push(self.desugar_predicate(pred, binders)?);
        }
        Ok(fhir::GenericPredicates { predicates: res })
    }

    fn desugar_predicate(
        &mut self,
        pred: &surface::WhereBoundPredicate,
        binders: &mut Binders,
    ) -> Result<fhir::WhereBoundPredicate, ErrorGuaranteed> {
        let bounded_ty = self.desugar_ty(None, &pred.bounded_ty, binders)?;
        let bounds = self.desugar_generic_bounds(&pred.bounds, binders)?;
        Ok(fhir::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
    }

    fn desugar_generic_bounds(
        &mut self,
        bounds: &surface::GenericBounds,
        binders: &mut Binders,
    ) -> Result<fhir::GenericBounds, ErrorGuaranteed> {
        bounds
            .iter()
            .map(|bound| {
                Ok(fhir::GenericBound::Trait(
                    self.desugar_trait_ref(bound, binders)?,
                    fhir::TraitBoundModifier::None,
                ))
            })
            .try_collect_exhaust()
    }

    fn desugar_trait_ref(
        &mut self,
        trait_ref: &surface::TraitRef,
        binders: &mut Binders,
    ) -> Result<fhir::PolyTraitRef, ErrorGuaranteed> {
        Ok(fhir::PolyTraitRef {
            bound_generic_params: vec![],
            trait_ref: self.desugar_path(&trait_ref.path, binders)?,
        })
    }

    pub(crate) fn desugar_struct_def(
        &mut self,
        struct_def: &surface::StructDef,
        binders: &mut Binders,
    ) -> Result<fhir::StructDef, ErrorGuaranteed> {
        binders.push_layer();
        binders.insert_params(
            self.genv,
            struct_def
                .refined_by
                .iter()
                .flat_map(surface::RefinedBy::all_params),
        )?;

        let invariants = struct_def
            .invariants
            .iter()
            .map(|invariant| self.as_expr_ctxt().desugar_expr(binders, invariant))
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
                            ty: self.desugar_ty(None, ty, binders)?,
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
            params: binders.pop_layer().into_params(self),
            kind,
            invariants,
        })
    }

    pub(crate) fn desugar_enum_def(
        &mut self,
        enum_def: &surface::EnumDef,
        binders: &mut Binders,
    ) -> Result<fhir::EnumDef, ErrorGuaranteed> {
        let def_id = self.owner.def_id;
        let ItemKind::Enum(hir_enum, _) = &self.genv.hir().expect_item(def_id).kind else {
            bug!("expected enum");
        };
        let variants = iter::zip(&enum_def.variants, hir_enum.variants)
            .map(|(variant, hir_variant)| {
                self.desugar_enum_variant_def(variant, hir_variant, binders)
            })
            .try_collect_exhaust()?;

        binders.push_layer();
        binders.insert_params(
            self.genv,
            enum_def
                .refined_by
                .iter()
                .flat_map(surface::RefinedBy::all_params),
        )?;

        let invariants = enum_def
            .invariants
            .iter()
            .map(|invariant| self.as_expr_ctxt().desugar_expr(binders, invariant))
            .try_collect_exhaust()?;

        Ok(fhir::EnumDef {
            owner_id: self.owner,
            params: binders.pop_layer().into_params(self),
            variants,
            invariants,
        })
    }

    fn desugar_enum_variant_def(
        &mut self,
        variant_def: &Option<surface::VariantDef>,
        hir_variant: &hir::Variant,
        binders: &mut Binders,
    ) -> Result<fhir::VariantDef, ErrorGuaranteed> {
        if let Some(variant_def) = variant_def {
            binders.push_layer();
            self.gather_params_variant(variant_def, binders)?;
            let fields = iter::zip(&variant_def.fields, hir_variant.data.fields())
                .map(|(ty, hir_field)| {
                    Ok(fhir::FieldDef {
                        ty: self.desugar_ty(None, ty, binders)?,
                        def_id: hir_field.def_id,
                        lifted: false,
                    })
                })
                .try_collect_exhaust()?;

            let ret = self.desugar_variant_ret(&variant_def.ret, binders)?;

            Ok(fhir::VariantDef {
                def_id: hir_variant.def_id,
                params: binders.pop_layer().into_params(self),
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
        binders: &mut Binders,
    ) -> Result<fhir::TyAlias, ErrorGuaranteed> {
        binders.push_layer();
        binders.insert_params(self.genv, ty_alias.refined_by.all_params())?;

        let ty = self.desugar_ty(None, &ty_alias.ty, binders)?;

        let mut early_bound_params = binders.pop_layer().into_params(self);
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
        binders: &mut Binders,
    ) -> Result<(fhir::GenericPredicates, fhir::FnSig), ErrorGuaranteed> {
        let mut requires = vec![];

        // Desugar inputs
        binders.push_layer();
        self.gather_input_params_fn_sig(fn_sig, binders)?;
        self.gather_params_predicates(&fn_sig.predicates, binders)?;

        // Desugar predicates -- after we have gathered the input params
        let generic_preds = self.desugar_predicates(&fn_sig.predicates, binders)?;

        if let Some(e) = &fn_sig.requires {
            let pred = self.as_expr_ctxt().desugar_expr(binders, e)?;
            requires.push(fhir::Constraint::Pred(pred));
        }

        // Bail out if there's an error in the arguments to avoid confusing error messages
        let args = fn_sig
            .args
            .iter()
            .map(|arg| self.desugar_fun_arg(arg, binders, &mut requires))
            .try_collect_exhaust()?;

        // Desugar output
        binders.push_layer();
        self.gather_output_params_fn_sig(fn_sig, binders)?;
        let ret = self.desugar_asyncness(fn_sig.asyncness, &fn_sig.returns, binders);

        let ensures = fn_sig
            .ensures
            .iter()
            .map(|cstr| self.desugar_constraint(cstr, binders))
            .try_collect_exhaust()?;

        let output =
            fhir::FnOutput { params: binders.pop_layer().into_params(self), ret: ret?, ensures };

        let fn_sig = fhir::FnSig {
            params: binders.pop_layer().into_params(self),
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
        binders: &mut Binders,
    ) -> Result<fhir::Constraint, ErrorGuaranteed> {
        match cstr {
            surface::Constraint::Type(bind, ty) => {
                let loc = self.as_expr_ctxt().resolve_loc(binders, *bind);
                let ty = self.desugar_ty(None, ty, binders);
                Ok(fhir::Constraint::Type(loc?, ty?))
            }
            surface::Constraint::Pred(e) => {
                let pred = self.as_expr_ctxt().desugar_expr(binders, e)?;
                Ok(fhir::Constraint::Pred(pred))
            }
        }
    }

    fn desugar_fun_arg(
        &mut self,
        arg: &surface::Arg,
        binders: &mut Binders,
        requires: &mut Vec<fhir::Constraint>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let bty = self.desugar_path_to_bty(path, binders)?;
                let pred = self.as_expr_ctxt().desugar_expr(binders, pred)?;

                let ty = if let Some(idx) = self.ident_into_refine_arg(*bind, binders)? {
                    fhir::Ty {
                        kind: fhir::TyKind::Indexed(bty, idx),
                        fhir_id: self.next_fhir_id(),
                        span: path.span,
                    }
                } else {
                    fhir::Ty {
                        kind: fhir::TyKind::BaseTy(bty),
                        fhir_id: self.next_fhir_id(),
                        span: path.span,
                    }
                };

                let span = path.span.to(pred.span);
                let kind = fhir::TyKind::Constr(pred, Box::new(ty));
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span })
            }
            surface::Arg::StrgRef(loc, ty) => {
                let span = loc.span;
                let loc = self.as_expr_ctxt().resolve_loc(binders, *loc)?;
                let ty = self.desugar_ty(None, ty, binders)?;
                requires.push(fhir::Constraint::Type(loc, ty));
                let kind = fhir::TyKind::Ptr(self.mk_lft_hole(), loc);
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span })
            }
            surface::Arg::Ty(bind, ty) => self.desugar_ty(*bind, ty, binders),
        }
    }

    fn desugar_asyncness(
        &mut self,
        asyncness: surface::Async,
        returns: &surface::FnRetTy,
        binders: &mut Binders,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match asyncness {
            surface::Async::Yes { node_id, span } => {
                let item_id = self.resolver_output.impl_trait_res_map[&node_id];
                let def_id = item_id.owner_id.def_id;
                let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

                let opaque_ty = self
                    .with_new_owner(item_id.owner_id)
                    .desugar_opaque_ty_for_async(returns, binders)?;
                self.insert_opaque_ty(item_id.owner_id.def_id, opaque_ty);

                let (args, _) = self.desugar_generic_args(res, &[], binders)?;
                let item_id = hir::ItemId { owner_id: hir::OwnerId { def_id } };
                let refine_args = binders.bot_layer().to_refine_args(self, span);
                let kind = fhir::TyKind::OpaqueDef(item_id, args, refine_args, false);
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span })
            }
            surface::Async::No => Ok(self.desugar_fn_ret_ty(returns, binders)?),
        }
    }

    fn desugar_opaque_ty_for_async(
        &mut self,
        returns: &surface::FnRetTy,
        binders: &mut Binders,
    ) -> Result<fhir::OpaqueTy, ErrorGuaranteed> {
        let output = self.desugar_fn_ret_ty(returns, binders)?;
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

    fn desugar_fn_ret_ty(
        &mut self,
        returns: &surface::FnRetTy,
        binders: &mut Binders,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match returns {
            surface::FnRetTy::Ty(ty) => self.desugar_ty(None, ty, binders),
            surface::FnRetTy::Default(span) => {
                let kind = fhir::TyKind::Tuple(vec![]);
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span: *span })
            }
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        binders: &mut Binders,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        let span = ty.span;
        let kind = match &ty.kind {
            surface::TyKind::Base(bty) => {
                // CODESYNC(type-holes, 3)
                if let surface::BaseTyKind::Path(path) = &bty.kind && path.is_hole() {
                    fhir::TyKind::Hole
                } else {
                    return self.desugar_bty_bind(bind, bty, binders)
                }
            }
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.desugar_bty(bty, binders)?;
                let idx = self.desugar_indices(&bty, indices, binders)?;
                fhir::TyKind::Indexed(bty, idx)
            }
            surface::TyKind::Exists { bind: ex_bind, bty, pred } => {
                let ty_span = ty.span;
                let bty_span = bty.span;

                let Some(sort) = index_sort(self.genv, self.resolver_output, bty) else {
                    return Err(self.emit_err(errors::RefinedUnrefinableType::new(bty.span)));
                };

                let bty = self.desugar_bty(bty, binders)?;

                binders.push_layer();
                let name = binders.fresh();
                let binder = Binder::Refined(name, sort, false);
                binders.insert_binder(self.sess(), *ex_bind, binder)?;
                let pred = self.as_expr_ctxt().desugar_expr(binders, pred)?;
                let params = binders.pop_layer().into_params(self);

                let idx = fhir::RefineArg::Expr {
                    expr: fhir::Expr {
                        kind: fhir::ExprKind::Var(params[0].ident),
                        span: ex_bind.span,
                        fhir_id: self.next_fhir_id(),
                    },
                    is_binder: false,
                };
                let indexed = fhir::Ty {
                    kind: fhir::TyKind::Indexed(bty, idx),
                    fhir_id: self.next_fhir_id(),
                    span: bty_span,
                };
                let constr = fhir::Ty {
                    kind: fhir::TyKind::Constr(pred, Box::new(indexed)),
                    fhir_id: self.next_fhir_id(),
                    span: ty_span,
                };
                fhir::TyKind::Exists(params, Box::new(constr))
            }
            surface::TyKind::GeneralExists { params, ty, pred } => {
                binders.push_layer();
                for param in params {
                    let fresh = binders.fresh();
                    let sort =
                        resolve_sort(self.sess(), self.genv.map().sort_decls(), &param.sort)?;
                    let binder = Binder::Refined(fresh, sort.clone(), false);
                    binders.insert_binder(self.sess(), param.name, binder)?;
                }

                let mut ty = self.desugar_ty(None, ty, binders)?;
                if let Some(pred) = pred {
                    let pred = self.as_expr_ctxt().desugar_expr(binders, pred)?;
                    let span = ty.span.to(pred.span);
                    ty = fhir::Ty {
                        kind: fhir::TyKind::Constr(pred, Box::new(ty)),
                        fhir_id: self.next_fhir_id(),
                        span,
                    };
                }
                let params = binders.pop_layer().into_params(self);

                fhir::TyKind::Exists(params, Box::new(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.as_expr_ctxt().desugar_expr(binders, pred)?;
                let ty = self.desugar_ty(None, ty, binders)?;
                fhir::TyKind::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let mut_ty = fhir::MutTy {
                    ty: Box::new(self.desugar_ty(None, ty, binders)?),
                    mutbl: *mutbl,
                };
                fhir::TyKind::Ref(self.mk_lft_hole(), mut_ty)
            }
            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.desugar_ty(None, ty, binders))
                    .try_collect_exhaust()?;
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(None, ty, binders)?;
                fhir::TyKind::Array(Box::new(ty), fhir::ArrayLen { val: len.val, span: len.span })
            }
            surface::TyKind::ImplTrait(node_id, bounds) => {
                let item_id = self.resolver_output.impl_trait_res_map[&node_id];
                let def_id = item_id.owner_id.def_id;
                let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

                let opaque_ty = self
                    .with_new_owner(item_id.owner_id)
                    .desugar_opaque_ty_for_impl_trait(bounds, binders)?;
                self.insert_opaque_ty(def_id, opaque_ty);

                let (args, _) = self.desugar_generic_args(res, &[], binders)?;
                let refine_args = binders.bot_layer().to_refine_args(self, ty.span);
                fhir::TyKind::OpaqueDef(item_id, args, refine_args, false)
            }
        };
        Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span })
    }

    fn desugar_opaque_ty_for_impl_trait(
        &mut self,
        bounds: &surface::GenericBounds,
        binders: &mut Binders,
    ) -> Result<fhir::OpaqueTy, ErrorGuaranteed> {
        let bounds = self.desugar_generic_bounds(bounds, binders)?;
        Ok(fhir::OpaqueTy { bounds })
    }

    fn mk_lft_hole(&self) -> fhir::Lifetime {
        fhir::Lifetime::Hole(self.next_fhir_id())
    }

    fn desugar_indices(
        &mut self,
        bty: &fhir::BaseTy,
        idxs: &surface::Indices,
        binders: &mut Binders,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        if let [surface::RefineArg::Bind(ident, ..)] = &idxs.indices[..] {
            self.ident_into_refine_arg(*ident, binders)
                .transpose()
                .unwrap()
        } else if let Some(fhir::Sort::Record(def_id)) = self.genv.sort_of_bty(bty) {
            let flds = self.desugar_refine_args(&idxs.indices, binders)?;
            Ok(fhir::RefineArg::Record(def_id, flds, idxs.span))
        } else if let [arg] = &idxs.indices[..] {
            self.desugar_refine_arg(arg, binders)
        } else {
            span_bug!(bty.span, "invalid index on non-record type")
        }
    }

    fn desugar_refine_args(
        &mut self,
        args: &[surface::RefineArg],
        binders: &mut Binders,
    ) -> Result<Vec<fhir::RefineArg>, ErrorGuaranteed> {
        args.iter()
            .map(|idx| self.desugar_refine_arg(idx, binders))
            .try_collect_exhaust()
    }

    fn desugar_refine_arg(
        &mut self,
        arg: &surface::RefineArg,
        binders: &mut Binders,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        match arg {
            surface::RefineArg::Bind(ident, ..) => {
                self.ident_into_refine_arg(*ident, binders)?
                    .ok_or_else(|| self.emit_err(errors::InvalidUnrefinedParam::new(*ident)))
            }
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg::Expr {
                    expr: self.as_expr_ctxt().desugar_expr(binders, expr)?,
                    is_binder: false,
                })
            }
            surface::RefineArg::Abs(params, body, span) => {
                binders.push_layer();
                binders.insert_params(self.genv, params)?;
                let body = self.as_expr_ctxt().desugar_expr(binders, body)?;
                let params = binders.pop_layer().into_params(self);
                Ok(fhir::RefineArg::Abs(params, body, *span, self.next_fhir_id()))
            }
        }
    }

    fn ident_into_refine_arg(
        &self,
        ident: surface::Ident,
        binders: &Binders,
    ) -> Result<Option<fhir::RefineArg>, ErrorGuaranteed> {
        match binders.get(ident) {
            Some(Binder::Refined(name, ..)) => {
                let kind = fhir::ExprKind::Var(fhir::Ident::new(*name, ident));
                let expr = fhir::Expr { kind, span: ident.span, fhir_id: self.next_fhir_id() };
                Ok(Some(fhir::RefineArg::Expr { expr, is_binder: true }))
            }
            Some(Binder::Unrefined) => Ok(None),
            None => Err(self.emit_err(errors::UnresolvedVar::from_ident(ident))),
        }
    }

    fn desugar_bty(
        &mut self,
        bty: &surface::BaseTy,
        binders: &mut Binders,
    ) -> Result<fhir::BaseTy, ErrorGuaranteed> {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.desugar_path_to_bty(path, binders),
            surface::BaseTyKind::Slice(ty) => {
                let kind = fhir::BaseTyKind::Slice(Box::new(self.desugar_ty(None, ty, binders)?));
                Ok(fhir::BaseTy { kind, span: bty.span })
            }
        }
    }

    fn desugar_path(
        &mut self,
        path: &surface::Path,
        binders: &mut Binders,
    ) -> Result<fhir::Path, ErrorGuaranteed> {
        let res = self.resolver_output.path_res_map[&path.node_id];
        let (args, bindings) = self.desugar_generic_args(res, &path.generics, binders)?;
        let refine = self.desugar_refine_args(&path.refine, binders)?;
        Ok(fhir::Path { res, args, bindings, refine, span: path.span })
    }

    fn desugar_path_to_bty(
        &mut self,
        path: &surface::Path,
        binders: &mut Binders,
    ) -> Result<fhir::BaseTy, ErrorGuaranteed> {
        Ok(fhir::BaseTy::from(fhir::QPath::Resolved(None, self.desugar_path(path, binders)?)))
    }

    fn desugar_generic_args(
        &mut self,
        res: Res,
        args: &[surface::GenericArg],
        binders: &mut Binders,
    ) -> Result<(Vec<fhir::GenericArg>, Vec<fhir::TypeBinding>), ErrorGuaranteed> {
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
                    fhir_args.push(fhir::GenericArg::Type(self.desugar_ty(None, ty, binders)?));
                }
                surface::GenericArg::Constraint(ident, ty) => {
                    bindings.push(fhir::TypeBinding {
                        ident: *ident,
                        term: self.desugar_ty(None, ty, binders)?,
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
        binders: &mut Binders,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        let bty = self.desugar_bty(bty, binders)?;
        let span = bty.span;
        let kind = if let Some(bind) = bind && let Some(idx) = self.ident_into_refine_arg(bind, binders)? {
            fhir::TyKind::Indexed(bty, idx)
        } else {
            fhir::TyKind::BaseTy(bty)
        };
        Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span })
    }

    fn desugar_variant_ret(
        &mut self,
        ret: &surface::VariantRet,
        binders: &mut Binders,
    ) -> Result<fhir::VariantRet, ErrorGuaranteed> {
        let bty = self.desugar_path_to_bty(&ret.path, binders)?;
        let idx = self.desugar_indices(&bty, &ret.indices, binders)?;
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

impl<'a, 'tcx> ExprCtxt<'a, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        owner: FluxOwnerId,
        local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
    ) -> Self {
        Self { genv, local_id_gen, owner }
    }

    fn desugar_expr(
        &self,
        binders: &Binders,
        expr: &surface::Expr,
    ) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match &expr.kind {
            surface::ExprKind::QPath(qpath) => {
                match self.resolve_qpath(binders, qpath)? {
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
                let e1 = self.desugar_expr(binders, e1);
                let e2 = self.desugar_expr(binders, e2);
                fhir::ExprKind::BinaryOp(desugar_bin_op(*op), Box::new([e1?, e2?]))
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(
                    desugar_un_op(*op),
                    Box::new(self.desugar_expr(binders, e)?),
                )
            }
            surface::ExprKind::Dot(qpath, fld) => {
                if let QPathRes::Param(ident) = self.resolve_qpath(binders, qpath)? {
                    fhir::ExprKind::Dot(ident, *fld)
                } else {
                    return Err(self.emit_err(errors::InvalidDotVar { span: expr.span }));
                }
            }
            surface::ExprKind::App(func, args) => {
                let args = self.desugar_exprs(binders, args)?;
                match self.resolve_func(binders, *func)? {
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
                let p = self.desugar_expr(binders, p);
                let e1 = self.desugar_expr(binders, e1);
                let e2 = self.desugar_expr(binders, e2);
                fhir::ExprKind::IfThenElse(Box::new([p?, e1?, e2?]))
            }
        };
        Ok(fhir::Expr { kind, span: expr.span, fhir_id: self.next_fhir_id() })
    }

    fn desugar_exprs(
        &self,
        binders: &Binders,
        exprs: &[surface::Expr],
    ) -> Result<Vec<fhir::Expr>, ErrorGuaranteed> {
        exprs
            .iter()
            .map(|e| self.desugar_expr(binders, e))
            .try_collect_exhaust()
    }

    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> Result<fhir::Lit, ErrorGuaranteed> {
        match lit.kind {
            surface::LitKind::Integer => {
                let Ok(n) = lit.symbol.as_str().parse::<i128>() else {
                    return Err(self.emit_err(errors::IntTooLarge { span }));
                };
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

    fn resolve_func(
        &self,
        binders: &Binders,
        func: surface::Ident,
    ) -> Result<FuncRes, ErrorGuaranteed> {
        match binders.get(func) {
            Some(Binder::Refined(name, ..)) => {
                return Ok(FuncRes::Param(fhir::Ident::new(*name, func)))
            }
            Some(Binder::Unrefined) => {
                return Err(self.emit_err(errors::InvalidUnrefinedParam::new(func)));
            }
            None => {}
        };
        if let Some(decl) = self.genv.func_decl(func.name) {
            return Ok(FuncRes::Global(decl));
        }
        Err(self.emit_err(errors::UnresolvedVar::from_ident(func)))
    }

    fn resolve_qpath(
        &self,
        binders: &Binders,
        qpath: &surface::QPathExpr,
    ) -> Result<QPathRes, ErrorGuaranteed> {
        match &qpath.segments[..] {
            [var] => {
                match binders.get(var) {
                    Some(Binder::Refined(name, ..)) => {
                        return Ok(QPathRes::Param(fhir::Ident::new(*name, *var)))
                    }
                    Some(Binder::Unrefined) => {
                        return Err(self.emit_err(errors::InvalidUnrefinedParam::new(*var)));
                    }
                    None => {}
                };
                if let Some(const_info) = self.genv.const_by_name(var.name) {
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

    fn resolve_loc(
        &self,
        binders: &Binders,
        loc: surface::Ident,
    ) -> Result<fhir::Ident, ErrorGuaranteed> {
        match binders.get(loc) {
            Some(Binder::Refined(name, ..)) => Ok(fhir::Ident::new(*name, loc)),
            Some(Binder::Unrefined) => Err(self.emit_err(errors::InvalidUnrefinedParam::new(loc))),
            None => Err(self.emit_err(errors::UnresolvedVar::from_ident(loc))),
        }
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess.emit_err(err)
    }
}

impl DesugarCtxt<'_, '_> {
    fn gather_params_variant(
        &self,
        variant_def: &surface::VariantDef,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        for ty in &variant_def.fields {
            self.gather_params_ty(None, ty, TypePos::Input, binders)?;
        }
        // Traverse `VariantRet` to find illegal binders and report invalid refinement errors.
        self.gather_params_variant_ret(&variant_def.ret, binders)?;

        // Check binders in `VariantRet`
        variant_def
            .ret
            .indices
            .indices
            .iter()
            .try_for_each_exhaust(|idx| {
                if let surface::RefineArg::Bind(_, kind, span) = idx {
                    Err(self.emit_err(errors::IllegalBinder::new(*span, *kind)))
                } else {
                    Ok(())
                }
            })
    }

    fn gather_params_variant_ret(
        &self,
        ret: &surface::VariantRet,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        self.gather_params_path(&ret.path, TypePos::Other, binders)?;
        let res = self.resolver_output.path_res_map[&ret.path.node_id];
        let Some(sort) = self.genv.sort_of_res(res) else {
            return Err(self.emit_err(errors::RefinedUnrefinableType::new(ret.path.span)));
        };
        self.gather_params_indices(sort, &ret.indices, TypePos::Other, binders)
    }

    fn gather_params_predicates(
        &self,
        predicates: &[surface::WhereBoundPredicate],
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        for predicate in predicates {
            self.gather_params_ty(None, &predicate.bounded_ty, TypePos::Other, binders)?;
            for bound in &predicate.bounds {
                self.gather_params_path(&bound.path, TypePos::Other, binders)?;
            }
        }
        Ok(())
    }

    fn gather_input_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        for param in fn_sig.generics.iter().flat_map(|g| &g.params) {
            let surface::GenericParamKind::Refine { sort } = &param.kind else { continue };
            binders.insert_binder(
                self.genv.sess,
                param.name,
                Binder::Refined(
                    binders.fresh(),
                    resolve_sort(self.genv.sess, self.genv.map().sort_decls(), sort)?,
                    false,
                ),
            )?;
        }
        for arg in &fn_sig.args {
            self.gather_params_fun_arg(arg, binders)?;
        }

        Ok(())
    }

    fn gather_output_params_fn_sig(
        &self,
        fn_sig: &surface::FnSig,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        if let surface::FnRetTy::Ty(ty) = &fn_sig.returns {
            self.gather_params_ty(None, ty, TypePos::Output, binders)?;
        }
        for cstr in &fn_sig.ensures {
            if let surface::Constraint::Type(_, ty) = cstr {
                self.gather_params_ty(None, ty, TypePos::Output, binders)?;
            };
        }
        Ok(())
    }

    fn gather_params_fun_arg(
        &self,
        arg: &surface::Arg,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                let res = self.resolver_output.path_res_map[&path.node_id];
                binders.insert_binder(
                    self.genv.sess,
                    *bind,
                    binders.binder_from_res(self.genv, res),
                )?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                binders.insert_binder(
                    self.genv.sess,
                    *loc,
                    Binder::Refined(binders.fresh(), fhir::Sort::Loc, false),
                )?;
                self.gather_params_ty(None, ty, TypePos::Input, binders)?;
            }
            surface::Arg::Ty(bind, ty) => {
                self.gather_params_ty(*bind, ty, TypePos::Input, binders)?;
            }
        }
        Ok(())
    }

    fn gather_params_ty(
        &self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty,
        pos: TypePos,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Indexed { bty, indices } => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                let Some(sort) = index_sort(self.genv, self.resolver_output, bty) else {
                    return Err(self.emit_err(errors::RefinedUnrefinableType::new(ty.span)));
                };
                self.gather_params_indices(sort, indices, pos, binders)?;
                self.gather_params_bty(bty, pos, binders)
            }
            surface::TyKind::Base(bty) => {
                if let Some(bind) = bind {
                    binders.insert_binder(
                        self.genv.sess,
                        bind,
                        binders.binder_from_bty(self.genv, self.resolver_output, bty),
                    )?;
                }
                self.gather_params_bty(bty, pos, binders)
            }

            surface::TyKind::Ref(_, ty) | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_ty(None, ty, pos, binders)
            }
            surface::TyKind::Tuple(tys) => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                for ty in tys {
                    self.gather_params_ty(None, ty, pos, binders)?;
                }
                Ok(())
            }
            surface::TyKind::Array(ty, _) => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_ty(None, ty, TypePos::Other, binders)
            }
            surface::TyKind::Exists { bty, .. } => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_bty(bty, pos, binders)
            }
            surface::TyKind::GeneralExists { ty, .. } => {
                if let Some(bind) = bind {
                    binders.insert_binder(self.genv.sess, bind, Binder::Unrefined)?;
                }
                // Declaring parameters with @ inside and existential has weird behavior if names
                // are being shadowed. Thus, we don't allow it to keep things simple. We could eventually
                // allow it if we resolve the weird behavior by detecting shadowing.
                self.gather_params_ty(None, ty, TypePos::Other, binders)
            }
            surface::TyKind::ImplTrait(_, bounds) => {
                for bound in bounds {
                    self.gather_params_path(&bound.path, TypePos::Other, binders)?;
                }
                Ok(())
            }
        }
    }

    fn gather_params_indices(
        &self,
        sort: fhir::Sort,
        indices: &surface::Indices,
        pos: TypePos,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        if let [surface::RefineArg::Bind(ident, kind, span)] = indices.indices[..] {
            if !pos.is_binder_allowed(kind) {
                return Err(self.emit_err(errors::IllegalBinder::new(span, kind)));
            }
            binders.insert_binder(self.genv.sess, ident, binders.binder_from_sort(sort))?;
        } else {
            let sorts = as_tuple(self.genv, &sort);
            if sorts.len() != indices.indices.len() {
                return Err(self.emit_err(errors::RefineArgCountMismatch::new(
                    indices.span,
                    sorts.len(),
                    indices.indices.len(),
                )));
            }

            for (idx, sort) in iter::zip(&indices.indices, sorts) {
                if let surface::RefineArg::Bind(ident, kind, span) = idx {
                    if !pos.is_binder_allowed(*kind) {
                        return Err(self.emit_err(errors::IllegalBinder::new(*span, *kind)));
                    }
                    binders.insert_binder(
                        self.genv.sess,
                        *ident,
                        binders.binder_from_sort(sort.clone()),
                    )?;
                }
            }
        }
        Ok(())
    }

    fn gather_params_path(
        &self,
        path: &surface::Path,
        pos: TypePos,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        // CODESYNC(type-holes, 3)
        if path.is_hole() {
            return Ok(());
        }
        let res = self.resolver_output.path_res_map[&path.node_id];
        let pos = if self.genv.is_box(res) { pos } else { TypePos::Other };
        path.generics
            .iter()
            .try_for_each_exhaust(|arg| self.gather_params_generic_arg(arg, pos, binders))
    }

    fn gather_params_generic_arg(
        &self,
        arg: &surface::GenericArg,
        pos: TypePos,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::GenericArg::Type(ty) => self.gather_params_ty(None, ty, pos, binders),
            surface::GenericArg::Constraint(_, ty) => self.gather_params_ty(None, ty, pos, binders),
        }
    }

    fn gather_params_bty(
        &self,
        bty: &surface::BaseTy,
        pos: TypePos,
        binders: &mut Binders,
    ) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.gather_params_path(path, pos, binders),
            surface::BaseTyKind::Slice(ty) => {
                self.gather_params_ty(None, ty, TypePos::Other, binders)
            }
        }
    }
}

fn resolve_sort(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    sort: &surface::Sort,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    match sort {
        surface::Sort::Base(sort) => resolve_base_sort(sess, sort_decls, sort),
        surface::Sort::Func { inputs, output } => {
            Ok(resolve_func_sort(sess, sort_decls, inputs, output)?.into())
        }
        surface::Sort::Infer => Ok(fhir::Sort::Wildcard),
    }
}

fn resolve_func_sort(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    inputs: &[surface::BaseSort],
    output: &surface::BaseSort,
) -> Result<fhir::FuncSort, ErrorGuaranteed> {
    let mut inputs_and_output: Vec<fhir::Sort> = inputs
        .iter()
        .map(|sort| resolve_base_sort(sess, sort_decls, sort))
        .try_collect_exhaust()?;
    inputs_and_output.push(resolve_base_sort(sess, sort_decls, output)?);
    Ok(fhir::FuncSort { inputs_and_output: List::from_vec(inputs_and_output) })
}

fn resolve_base_sort(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    base: &surface::BaseSort,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    match base {
        surface::BaseSort::Ident(ident) => resolve_base_sort_ident(sess, sort_decls, ident),
        surface::BaseSort::BitVec(w) => Ok(fhir::Sort::BitVec(*w)),
        surface::BaseSort::App(ident, args) => resolve_app_sort(sess, sort_decls, *ident, args),
    }
}

fn resolve_sort_ctor(
    sess: &FluxSession,
    ident: surface::Ident,
) -> Result<fhir::SortCtor, ErrorGuaranteed> {
    if ident.name == SORTS.set {
        Ok(fhir::SortCtor::Set)
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(ident)))
    }
}

fn resolve_app_sort(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    ident: surface::Ident,
    args: &Vec<surface::BaseSort>,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    let ctor = resolve_sort_ctor(sess, ident)?;
    let arity = ctor.arity();
    if args.len() == arity {
        let args = args
            .iter()
            .map(|arg| resolve_base_sort(sess, sort_decls, arg))
            .try_collect_exhaust()?;
        Ok(fhir::Sort::App(ctor, args))
    } else {
        Err(sess.emit_err(errors::SortArityMismatch::new(ident.span, arity, args.len())))
    }
}

fn resolve_base_sort_ident(
    sess: &FluxSession,
    sort_decls: &fhir::SortDecls,
    ident: &surface::Ident,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    if ident.name == SORTS.int {
        Ok(fhir::Sort::Int)
    } else if ident.name == sym::bool {
        Ok(fhir::Sort::Bool)
    } else if ident.name == SORTS.real {
        Ok(fhir::Sort::Real)
    } else if sort_decls.get(&ident.name).is_some() {
        let ctor = fhir::SortCtor::User { name: ident.name, arity: 0 };
        Ok(fhir::Sort::App(ctor, List::empty()))
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(*ident)))
    }
}

impl Binders {
    pub(crate) fn new() -> Binders {
        Binders { name_gen: IndexGen::new(), layers: vec![] }
    }

    fn from_params<'a>(
        genv: &GlobalEnv,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<Self, ErrorGuaranteed> {
        let mut binders = Self::new();
        binders.push_layer();
        binders.insert_params(genv, params)?;
        Ok(binders)
    }

    fn insert_params<'a>(
        &mut self,
        genv: &GlobalEnv,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<(), ErrorGuaranteed> {
        for param in params {
            self.insert_binder(
                genv.sess,
                param.name,
                Binder::Refined(
                    self.fresh(),
                    resolve_sort(genv.sess, genv.map().sort_decls(), &param.sort)?,
                    false,
                ),
            )?;
        }
        Ok(())
    }

    fn fresh(&self) -> fhir::Name {
        self.name_gen.fresh()
    }

    fn get(&self, ident: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.iter_layers(|layer| layer.get(ident.borrow()))
    }

    fn insert_binder(
        &mut self,
        sess: &FluxSession,
        ident: surface::Ident,
        binder: Binder,
    ) -> Result<(), ErrorGuaranteed> {
        self.top_layer().insert(sess, ident, binder)
    }

    fn bot_layer(&mut self) -> &mut Layer {
        self.layers.first_mut().unwrap()
    }

    fn top_layer(&mut self) -> &mut Layer {
        self.layers.last_mut().unwrap()
    }

    fn iter_layers<'a, T>(&'a self, f: impl FnMut(&'a Layer) -> Option<T>) -> Option<T> {
        self.layers.iter().rev().find_map(f)
    }

    fn push_layer(&mut self) {
        self.layers.push(Layer::default());
    }

    fn pop_layer(&mut self) -> Layer {
        self.layers.pop().unwrap()
    }

    fn binder_from_sort(&self, sort: fhir::Sort) -> Binder {
        Binder::Refined(self.fresh(), sort, true)
    }

    fn binder_from_res(&self, genv: &GlobalEnv, res: fhir::Res) -> Binder {
        if let Some(sort) = genv.sort_of_res(res) {
            self.binder_from_sort(sort)
        } else {
            Binder::Unrefined
        }
    }

    fn binder_from_bty(
        &self,
        genv: &GlobalEnv,
        resolver_output: &ResolverOutput,
        bty: &surface::BaseTy,
    ) -> Binder {
        if let Some(sort) = index_sort(genv, resolver_output, bty) {
            self.binder_from_sort(sort)
        } else {
            Binder::Unrefined
        }
    }
}

impl<T: Borrow<surface::Ident>> std::ops::Index<T> for Binders {
    type Output = Binder;

    fn index(&self, index: T) -> &Self::Output {
        self.get(index).unwrap()
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

impl Layer {
    fn get(&self, key: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.map.get(key.borrow())
    }

    fn insert(
        &mut self,
        sess: &FluxSession,
        ident: surface::Ident,
        binder: Binder,
    ) -> Result<(), ErrorGuaranteed> {
        match self.map.entry(ident) {
            IndexEntry::Occupied(entry) => {
                Err(sess.emit_err(errors::DuplicateParam::new(*entry.key(), ident)))
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(binder);
                Ok(())
            }
        }
    }

    fn to_refine_args<'a, 'tcx>(
        &self,
        cx: &impl DesugarContext<'a, 'tcx>,
        span: Span,
    ) -> Vec<fhir::RefineArg> {
        let mut refine_args = vec![];
        for (ident, binder) in self.map.iter() {
            match binder {
                Binder::Refined(name, _, _) => {
                    let ident = fhir::Ident::new(*name, *ident);
                    let kind = ExprKind::Var(ident);
                    let fhir_id = cx.next_fhir_id();
                    let expr = fhir::Expr { kind, span, fhir_id };
                    refine_args.push(fhir::RefineArg::Expr { expr, is_binder: false });
                }
                Binder::Unrefined => {}
            }
        }
        refine_args
    }

    fn into_params<'a, 'tcx>(self, cx: &impl DesugarContext<'a, 'tcx>) -> Vec<fhir::RefineParam> {
        let mut params = vec![];
        for (ident, binder) in self.map {
            match binder {
                Binder::Refined(name, sort, implicit) => {
                    let ident = fhir::Ident::new(name, ident);
                    let fhir_id = cx.next_fhir_id();
                    params.push(fhir::RefineParam { ident, sort, implicit, fhir_id });
                }
                Binder::Unrefined => {}
            }
        }
        params
    }
}

fn index_sort(
    genv: &GlobalEnv,
    resolver_output: &ResolverOutput,
    bty: &surface::BaseTy,
) -> Option<fhir::Sort> {
    match &bty.kind {
        surface::BaseTyKind::Path(path) => {
            let res = resolver_output.path_res_map[&path.node_id];
            genv.sort_of_res(res)
        }
        surface::BaseTyKind::Slice(_) => Some(fhir::Sort::Int),
    }
}

fn as_tuple<'a>(genv: &'a GlobalEnv, sort: &'a fhir::Sort) -> &'a [fhir::Sort] {
    if let fhir::Sort::Record(def_id) = sort {
        genv.index_sorts_of(*def_id)
    } else {
        slice::from_ref(sort)
    }
}

trait DesugarContext<'a, 'tcx> {
    fn next_fhir_id(&self) -> FhirId;
}

impl<'a, 'tcx> DesugarContext<'a, 'tcx> for DesugarCtxt<'a, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
    }
}

impl<'a, 'tcx> DesugarContext<'a, 'tcx> for ExprCtxt<'a, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: self.owner, local_id: self.local_id_gen.fresh() }
    }
}

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

struct Sorts {
    int: Symbol,
    real: Symbol,
    set: Symbol,
}

static SORTS: std::sync::LazyLock<Sorts> = std::sync::LazyLock::new(|| {
    Sorts { int: Symbol::intern("int"), real: Symbol::intern("real"), set: Symbol::intern("Set") }
});

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface::{BindKind, QPathExpr};
    use itertools::Itertools;
    use rustc_span::{symbol::Ident, Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_var, code = "FLUX")]
    pub(super) struct UnresolvedVar {
        #[primary_span]
        #[label]
        span: Span,
        var: String,
    }

    impl UnresolvedVar {
        pub(super) fn from_qpath(qpath: &QPathExpr) -> Self {
            Self {
                span: qpath.span,
                var: format!("{}", qpath.segments.iter().format_with("::", |s, f| f(&s.name))),
            }
        }

        pub(super) fn from_ident(ident: Ident) -> Self {
            Self { span: ident.span, var: format!("{ident}") }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_duplicate_param, code = "FLUX")]
    pub(super) struct DuplicateParam {
        #[primary_span]
        #[label]
        span: Span,
        name: Symbol,
        #[label(desugar_first_use)]
        first_use: Span,
    }

    impl DuplicateParam {
        pub(super) fn new(old_ident: Ident, new_ident: Ident) -> Self {
            debug_assert_eq!(old_ident.name, new_ident.name);
            Self { span: new_ident.span, name: new_ident.name, first_use: old_ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_sort, code = "FLUX")]
    pub(super) struct UnresolvedSort {
        #[primary_span]
        #[label]
        span: Span,
        sort: Ident,
    }

    impl UnresolvedSort {
        pub(super) fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_int_too_large, code = "FLUX")]
    pub(super) struct IntTooLarge {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unexpected_literal, code = "FLUX")]
    pub(super) struct UnexpectedLiteral {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar_invalid_dot_var, code = "FLUX")]
    pub(super) struct InvalidDotVar {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar_sort_arity_mismatch, code = "FLUX")]
    pub(super) struct SortArityMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: usize,
        found: usize,
    }

    impl SortArityMismatch {
        pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_refine_arg_count_mismatch, code = "FLUX")]
    pub(super) struct RefineArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: usize,
        found: usize,
    }

    impl RefineArgCountMismatch {
        pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_invalid_unrefined_param, code = "FLUX")]
    pub(super) struct InvalidUnrefinedParam {
        #[primary_span]
        #[label]
        span: Span,
        var: Ident,
    }

    impl InvalidUnrefinedParam {
        pub(super) fn new(var: Ident) -> Self {
            Self { var, span: var.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_illegal_binder, code = "FLUX")]
    pub(super) struct IllegalBinder {
        #[primary_span]
        #[label]
        span: Span,
        kind: &'static str,
    }

    impl IllegalBinder {
        pub(super) fn new(span: Span, kind: BindKind) -> Self {
            Self { span, kind: kind.token_str() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_invalid_numeric_suffix, code = "FLUX")]
    pub(super) struct InvalidNumericSuffix {
        #[primary_span]
        #[label]
        span: Span,
        suffix: Symbol,
    }

    impl InvalidNumericSuffix {
        pub(super) fn new(span: Span, suffix: Symbol) -> Self {
            Self { span, suffix }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_refined_unrefinable_type, code = "FLUX")]
    pub(super) struct RefinedUnrefinableType {
        #[primary_span]
        span: Span,
    }

    impl RefinedUnrefinableType {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_generic_param, code = "FLUX")]
    #[note]
    pub(super) struct UnresolvedGenericParam {
        #[primary_span]
        span: Span,
    }

    impl UnresolvedGenericParam {
        pub(super) fn new(param: Ident) -> Self {
            Self { span: param.span }
        }
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
