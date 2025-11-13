mod lift;

use std::iter;

use flux_common::{
    bug, dbg,
    index::IndexGen,
    iter::IterExt,
    result::{ErrorCollector, ErrorEmitter},
    span_bug,
};
use flux_config as config;
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    ResolverOutput,
    def_id::{FluxLocalDefId, MaybeExternId},
    fhir::{self, FhirId, FluxOwnerId, ParamId, QPathExpr, Res},
    global_env::GlobalEnv,
    query_bug, try_alloc_slice,
};
use flux_syntax::{
    surface::{self, ConstructorArg, NodeId, visit::Visitor as _},
    symbols::{kw, sym},
    walk_list,
};
use hir::{ItemKind, def::DefKind};
use itertools::{Either, Itertools};
use rustc_data_structures::fx::FxIndexSet;
use rustc_errors::{Diagnostic, ErrorGuaranteed};
use rustc_hash::FxHashSet;
use rustc_hir::{self as hir, OwnerId, def::Namespace};
use rustc_span::{
    DUMMY_SP, Span,
    def_id::{DefId, LocalDefId},
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

use crate::errors;

/// Collect all sorts resolved to a generic type in a list of refinement parameters. Return the set
/// of generic def_ids used (sorted by their position in the list of generics).
fn collect_generics_in_params(
    genv: GlobalEnv,
    owner: MaybeExternId<OwnerId>,
    resolver_output: &ResolverOutput,
    params: &surface::RefineParams,
) -> FxIndexSet<DefId> {
    struct ParamCollector<'a> {
        resolver_output: &'a ResolverOutput,
        found: FxHashSet<DefId>,
    }
    impl surface::visit::Visitor for ParamCollector<'_> {
        fn visit_base_sort(&mut self, bsort: &surface::BaseSort) {
            if let surface::BaseSort::Path(path) = bsort {
                let res = self.resolver_output.sort_path_res_map[&path.node_id];
                if let fhir::SortRes::TyParam(def_id) = res {
                    self.found.insert(def_id);
                }
            }
            surface::visit::walk_base_sort(self, bsort);
        }
    }
    let mut vis = ParamCollector { resolver_output, found: FxHashSet::default() };
    walk_list!(vis, visit_refine_param, params);
    genv.tcx()
        .generics_of(owner.resolved_id())
        .own_params
        .iter()
        .filter_map(
            |param| if vis.found.contains(&param.def_id) { Some(param.def_id) } else { None },
        )
        .collect()
}

pub(crate) struct RustItemCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: MaybeExternId<OwnerId>,
    fn_sig_scope: Option<NodeId>,
    resolver_output: &'genv ResolverOutput,
    /// HACK! We assume there's at most one opaque type (we fail with an error if there's more than one)
    /// and we store the `DefId` here if it exists. See [`collect_opaque_types`]
    opaque: Option<LocalDefId>,
    /// This collects all the opaque types generated in the process of desugaring an `FnSig`, however
    /// we can only resolve one opaque type so this will contain at most one element.
    opaque_tys: Option<&'a mut Vec<&'genv fhir::OpaqueTy<'genv>>>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx: 'genv> RustItemCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn with<T>(
        genv: GlobalEnv<'genv, 'tcx>,
        owner: MaybeExternId<OwnerId>,
        resolver_output: &'genv ResolverOutput,
        opaque_tys: Option<&'a mut Vec<&'genv fhir::OpaqueTy<'genv>>>,
        f: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let mut cx = RustItemCtxt {
            genv,
            owner,
            fn_sig_scope: None,
            local_id_gen: IndexGen::new(),
            resolver_output,
            opaque_tys,
            errors: Errors::new(genv.sess()),
            opaque: collect_opaque_types(genv, owner)?,
        };
        let r = f(&mut cx)?;
        cx.into_result()?;
        Ok(r)
    }

    pub(crate) fn desugar_item(&mut self, item: &surface::Item) -> Result<fhir::Item<'genv>> {
        match &item.kind {
            surface::ItemKind::Fn(fn_sig) => {
                let (generics, fn_sig) = self.desugar_fn_sig(fn_sig.as_ref())?;
                Ok(fhir::Item { generics, kind: fhir::ItemKind::Fn(fn_sig), owner_id: self.owner })
            }
            surface::ItemKind::Struct(struct_def) => Ok(self.desugar_struct_def(struct_def)),
            surface::ItemKind::Enum(enum_def) => self.desugar_enum_def(enum_def),
            surface::ItemKind::Trait(trait_) => self.desugar_trait(trait_),
            surface::ItemKind::Impl(impl_) => Ok(self.desugar_impl(impl_)),
            surface::ItemKind::Const(constant_info) => Ok(self.desugar_const(constant_info)),
            surface::ItemKind::TyAlias(ty_alias) => Ok(self.desugar_type_alias(ty_alias)),
            surface::ItemKind::Mod => Err(self.emit(query_bug!("modules can't be desugared"))),
        }
    }

    pub(crate) fn desugar_trait_item(
        &mut self,
        item: &surface::TraitItemFn,
    ) -> Result<fhir::TraitItem<'genv>> {
        let (generics, fn_sig) = self.desugar_fn_sig(item.sig.as_ref())?;
        Ok(fhir::TraitItem {
            generics,
            kind: fhir::TraitItemKind::Fn(fn_sig),
            owner_id: self.owner,
        })
    }

    pub(crate) fn desugar_impl_item(
        &mut self,
        item: &surface::ImplItemFn,
    ) -> Result<fhir::ImplItem<'genv>> {
        let (generics, fn_sig) = self.desugar_fn_sig(item.sig.as_ref())?;
        Ok(fhir::ImplItem { generics, kind: fhir::ImplItemKind::Fn(fn_sig), owner_id: self.owner })
    }

    fn desugar_trait(&mut self, trait_: &surface::Trait) -> Result<fhir::Item<'genv>> {
        let generics = if let Some(generics) = &trait_.generics {
            self.desugar_generics(generics)
        } else {
            self.lift_generics()
        };
        let assoc_refinements = self.desugar_trait_assoc_refts(&trait_.assoc_refinements)?;
        let trait_ = fhir::Trait { assoc_refinements };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &trait_).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Trait(trait_), owner_id: self.owner })
    }

    fn desugar_trait_assoc_refts(
        &mut self,
        assoc_refts: &[surface::TraitAssocReft],
    ) -> Result<&'genv [fhir::TraitAssocReft<'genv>]> {
        let iter = assoc_refts
            .iter()
            .map(|assoc_reft| {
                let name = assoc_reft.name.name;
                let params = self.desugar_refine_params(&assoc_reft.params);
                let output = self.desugar_base_sort(&assoc_reft.output, None);
                let body = assoc_reft.body.as_ref().map(|expr| self.desugar_expr(expr));
                if body.is_none() && assoc_reft.final_ {
                    Err(self.emit(errors::FinalAssocReftWithoutBody::new(assoc_reft.span)))
                } else {
                    Ok(fhir::TraitAssocReft {
                        name,
                        params,
                        output,
                        body,
                        span: assoc_reft.span,
                        final_: assoc_reft.final_,
                    })
                }
            })
            .try_collect_vec()?
            .into_iter();
        Ok(self.genv().alloc_slice_fill_iter(iter))
    }

    fn desugar_impl(&mut self, impl_: &surface::Impl) -> fhir::Item<'genv> {
        let generics = if let Some(generics) = &impl_.generics {
            self.desugar_generics(generics)
        } else {
            self.lift_generics()
        };
        let assoc_refinements = self.desugar_impl_assoc_refts(&impl_.assoc_refinements);
        let impl_ = fhir::Impl { assoc_refinements };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &impl_).unwrap();
        }

        fhir::Item { generics, kind: fhir::ItemKind::Impl(impl_), owner_id: self.owner }
    }

    fn desugar_impl_assoc_refts(
        &mut self,
        assoc_refts: &[surface::ImplAssocReft],
    ) -> &'genv [fhir::ImplAssocReft<'genv>] {
        self.genv()
            .alloc_slice_fill_iter(assoc_refts.iter().map(|assoc_reft| {
                let name = assoc_reft.name.name;
                let body = self.desugar_expr(&assoc_reft.body);
                let params = self.desugar_refine_params(&assoc_reft.params);
                let output = self.desugar_base_sort(&assoc_reft.output, None);
                fhir::ImplAssocReft { name, params, output, body, span: assoc_reft.span }
            }))
    }

    fn desugar_generics(&mut self, generics: &surface::Generics) -> fhir::Generics<'genv> {
        let params = self.genv.alloc_slice_fill_iter(
            self.genv
                .tcx()
                .hir_get_generics(self.owner.local_id().def_id)
                .unwrap()
                .params
                .iter()
                .map(|hir_param| self.lift_generic_param(hir_param)),
        );

        let predicates = generics
            .predicates
            .as_ref()
            .map(|preds| self.desugar_generic_predicates(preds));
        fhir::Generics { params, refinement_params: &[], predicates }
    }

    fn desugar_opt_generics(
        &mut self,
        generics: Option<&surface::Generics>,
    ) -> fhir::Generics<'genv> {
        if let Some(generics) = generics {
            self.desugar_generics(generics)
        } else {
            self.lift_generics()
        }
    }

    fn desugar_generic_predicates(
        &mut self,
        predicates: &[surface::WhereBoundPredicate],
    ) -> &'genv [fhir::WhereBoundPredicate<'genv>] {
        self.genv
            .alloc_slice_fill_iter(predicates.iter().map(|pred| {
                let bounded_ty = self.desugar_ty(&pred.bounded_ty);
                let bounds = self.desugar_generic_bounds(&pred.bounds);
                fhir::WhereBoundPredicate { span: pred.span, bounded_ty, bounds }
            }))
    }

    fn desugar_generic_bounds(
        &mut self,
        bounds: &[surface::TraitRef],
    ) -> fhir::GenericBounds<'genv> {
        self.genv().alloc_slice_fill_iter(
            bounds
                .iter()
                .map(|bound| fhir::GenericBound::Trait(self.desugar_trait_ref(bound))),
        )
    }

    fn desugar_trait_ref(&mut self, trait_ref: &surface::TraitRef) -> fhir::PolyTraitRef<'genv> {
        let fhir::QPath::Resolved(None, path) = self.desugar_qpath(None, &trait_ref.path) else {
            span_bug!(trait_ref.path.span, "desugar_alias_reft: unexpected qpath")
        };
        let span = path.span;

        let refine_params = self
            .genv
            .alloc_slice_fill_iter(self.implicit_params_to_params(trait_ref.node_id));

        fhir::PolyTraitRef {
            bound_generic_params: &[],
            refine_params,
            modifiers: fhir::TraitBoundModifier::None,
            trait_ref: path,
            span,
        }
    }

    fn desugar_refined_by(&mut self, refined_by: &surface::RefineParams) -> fhir::RefinedBy<'genv> {
        let generic_id_to_var_idx =
            collect_generics_in_params(self.genv, self.owner, self.resolver_output, refined_by);

        let fields = refined_by
            .iter()
            .map(|param| {
                (param.ident.name, self.desugar_sort(&param.sort, Some(&generic_id_to_var_idx)))
            })
            .collect();

        fhir::RefinedBy::new(fields, generic_id_to_var_idx)
    }

    fn desugar_struct_def(&mut self, struct_def: &surface::StructDef) -> fhir::Item<'genv> {
        let refined_by = if let Some(refined_by) = &struct_def.refined_by {
            self.desugar_refined_by(refined_by)
        } else {
            fhir::RefinedBy::trivial()
        };

        let generics = self.desugar_opt_generics(struct_def.generics.as_ref());

        let invariants = self.genv().alloc_slice_fill_iter(
            struct_def
                .invariants
                .iter()
                .map(|invariant| self.desugar_expr(invariant)),
        );

        let kind = if struct_def.opaque {
            fhir::StructKind::Opaque
        } else {
            let kind = &self
                .genv
                .tcx()
                .hir_expect_item(self.owner.local_id().def_id)
                .kind;
            match kind {
                hir::ItemKind::Struct(_, _, variant_data)
                | hir::ItemKind::Union(_, _, variant_data) => {
                    debug_assert_eq!(struct_def.fields.len(), variant_data.fields().len());
                    let fields = self.genv.alloc_slice_fill_iter(
                        iter::zip(&struct_def.fields, variant_data.fields()).map(
                            |(ty, hir_field)| {
                                if let Some(ty) = ty {
                                    fhir::FieldDef { ty: self.desugar_ty(ty), lifted: false }
                                } else {
                                    self.lift_field_def(hir_field)
                                }
                            },
                        ),
                    );
                    fhir::StructKind::Transparent { fields }
                }
                _ => bug!("expected struct or union"),
            }
        };

        let params = self.desugar_refine_params(struct_def.refined_by.as_deref().unwrap_or(&[]));
        let refinement = fhir::RefinementKind::Refined(refined_by);
        let struct_def =
            fhir::StructDef { refinement: self.genv.alloc(refinement), params, kind, invariants };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", struct_def)
                .unwrap();
        }

        fhir::Item { generics, kind: fhir::ItemKind::Struct(struct_def), owner_id: self.owner }
    }

    fn desugar_enum_def(&mut self, enum_def: &surface::EnumDef) -> Result<fhir::Item<'genv>> {
        let def_id = self.owner.local_id().def_id;
        let ItemKind::Enum(_, _, hir_enum) = self.genv.tcx().hir_expect_item(def_id).kind else {
            bug!("expected enum");
        };
        let reflected = enum_def.reflected;
        let variants = try_alloc_slice!(
            self.genv,
            iter::zip(&enum_def.variants, hir_enum.variants),
            |(variant, hir_variant)| self.desugar_enum_variant_def(reflected, variant, hir_variant)
        )?;

        let kind = if enum_def.reflected {
            fhir::RefinementKind::Reflected
        } else if let Some(refined_by) = &enum_def.refined_by {
            fhir::RefinementKind::Refined(self.desugar_refined_by(refined_by))
        } else {
            fhir::RefinementKind::Refined(fhir::RefinedBy::trivial())
        };

        let generics = self.desugar_opt_generics(enum_def.generics.as_ref());

        let invariants = self.genv().alloc_slice_fill_iter(
            enum_def
                .invariants
                .iter()
                .map(|invariant| self.desugar_expr(invariant)),
        );

        let params = self.desugar_refine_params(enum_def.refined_by.as_deref().unwrap_or(&[]));
        let enum_def =
            fhir::EnumDef { refinement: self.genv.alloc(kind), params, variants, invariants };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &enum_def).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Enum(enum_def), owner_id: self.owner })
    }

    fn desugar_enum_variant_def(
        &mut self,
        reflected: bool,
        variant_def: &Option<surface::VariantDef>,
        hir_variant: &hir::Variant,
    ) -> Result<fhir::VariantDef<'genv>> {
        if let Some(variant_def) = variant_def {
            if reflected {
                return Err(self.emit(errors::InvalidReflectedVariant::new(hir_variant.span)));
            }
            let fields = self.genv.alloc_slice_fill_iter(
                variant_def
                    .fields
                    .iter()
                    .map(|ty| fhir::FieldDef { ty: self.desugar_ty(ty), lifted: false }),
            );

            let ret = if let Some(ret) = &variant_def.ret {
                self.desugar_variant_ret(ret)?
            } else {
                self.lift_variant_ret()
            };

            let params = self
                .genv
                .alloc_slice_fill_iter(self.implicit_params_to_params(variant_def.node_id));

            Ok(fhir::VariantDef {
                def_id: hir_variant.def_id,
                params,
                fields,
                ret,
                span: variant_def.span,
                lifted: false,
            })
        } else {
            Ok(self.lift_enum_variant(hir_variant))
        }
    }

    fn desugar_type_alias(&mut self, ty_alias: &surface::TyAlias) -> fhir::Item<'genv> {
        let mut generics = self.desugar_generics(&ty_alias.generics);

        let ty = self.desugar_ty(&ty_alias.ty);

        generics.refinement_params = self.desugar_refine_params(&ty_alias.params);

        let index = ty_alias
            .index
            .as_ref()
            .map(|index| self.desugar_refine_param(index));

        let ty_alias =
            self.genv()
                .alloc(fhir::TyAlias { index, ty, span: ty_alias.span, lifted: false });
        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", ty_alias).unwrap();
        }
        fhir::Item { generics, kind: fhir::ItemKind::TyAlias(ty_alias), owner_id: self.owner }
    }

    fn desugar_const(&mut self, const_info: &surface::ConstantInfo) -> fhir::Item<'genv> {
        let expr = const_info.expr.as_ref().map(|e| self.desugar_expr(e));
        let owner_id = self.owner;
        let generics = self.lift_generics();
        let kind = fhir::ItemKind::Const(expr);
        fhir::Item { owner_id, generics, kind }
    }

    fn desugar_fn_sig(
        &mut self,
        fn_sig: Option<&surface::FnSig>,
    ) -> Result<(fhir::Generics<'genv>, fhir::FnSig<'genv>)> {
        let mut header = self.lift_fn_header();
        let (generics, decl) = if let Some(fn_sig) = fn_sig {
            self.fn_sig_scope = Some(fn_sig.node_id);

            let mut requires = vec![];

            let mut generics = self.desugar_generics(&fn_sig.generics);

            for surface_requires in &fn_sig.requires {
                let params = self.desugar_refine_params(&surface_requires.params);
                let pred = self.desugar_expr(&surface_requires.pred);
                requires.push(fhir::Requires { params, pred });
            }

            // Bail out if there's an error in the arguments to avoid confusing error messages
            let inputs = self
                .genv()
                .alloc_slice_fill_iter(fn_sig.inputs.iter().map(|arg| self.desugar_fn_input(arg)));

            let output = self.desugar_fn_output(fn_sig.asyncness, &fn_sig.output)?;

            generics.refinement_params = self.desugar_fn_sig_refine_params(fn_sig);

            let decl = fhir::FnDecl {
                requires: self.genv.alloc_slice(&requires),
                inputs,
                output,
                span: fn_sig.span,
                lifted: false,
            };
            // Fix up the span in asyncness
            if let surface::Async::Yes { span, .. } = fn_sig.asyncness {
                header.asyncness = hir::IsAsync::Async(span);
            }
            (generics, decl)
        } else {
            (self.lift_generics(), self.lift_fn_decl())
        };
        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", decl).unwrap();
        }
        Ok((generics, fhir::FnSig { header, decl: self.genv.alloc(decl) }))
    }

    fn desugar_fn_sig_refine_params(
        &mut self,
        fn_sig: &surface::FnSig,
    ) -> &'genv [fhir::RefineParam<'genv>] {
        let genv = self.genv;
        let mut params = self
            .desugar_refine_params_iter(&fn_sig.params)
            .collect_vec();
        params.extend(self.implicit_params_to_params(fn_sig.node_id));

        genv.alloc_slice(&params)
    }

    fn desugar_fn_output(
        &mut self,
        asyncness: surface::Async,
        output: &surface::FnOutput,
    ) -> Result<fhir::FnOutput<'genv>> {
        let ret = self.desugar_asyncness(asyncness, &output.returns);

        let ensures = try_alloc_slice!(self.genv, &output.ensures, |it| self.desugar_ensures(it))?;

        let params = self
            .genv
            .alloc_slice_fill_iter(self.implicit_params_to_params(output.node_id));
        Ok(fhir::FnOutput { params, ret, ensures })
    }

    fn desugar_ensures(&mut self, cstr: &surface::Ensures) -> Result<fhir::Ensures<'genv>> {
        match cstr {
            surface::Ensures::Type(loc, ty, node_id) => {
                let res = self.desugar_loc(*loc, *node_id)?;
                let path = fhir::PathExpr {
                    segments: self.genv().alloc_slice(&[*loc]),
                    res,
                    fhir_id: self.next_fhir_id(),
                    span: loc.span,
                };
                let ty = self.desugar_ty(ty);
                Ok(fhir::Ensures::Type(path, self.genv().alloc(ty)))
            }
            surface::Ensures::Pred(e) => {
                let pred = self.desugar_expr(e);
                Ok(fhir::Ensures::Pred(pred))
            }
        }
    }

    fn desugar_fn_input(&mut self, input: &surface::FnInput) -> fhir::Ty<'genv> {
        match input {
            surface::FnInput::Constr(bind, path, pred, node_id) => {
                let bty = self.desugar_path_to_bty(None, path);

                let pred = self.desugar_expr(pred);

                let ty = if let Some(idx) = self.implicit_param_into_refine_arg(*bind, *node_id) {
                    fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: path.span }
                } else {
                    fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: path.span }
                };

                let span = path.span.to(pred.span);
                let kind = fhir::TyKind::Constr(pred, self.genv.alloc(ty));
                fhir::Ty { kind, span }
            }
            surface::FnInput::StrgRef(loc, ty, node_id) => {
                let span = loc.span;
                let (id, kind) = self.resolve_implicit_param(*node_id).unwrap();
                let path = fhir::PathExpr {
                    segments: self.genv.alloc_slice(&[*loc]),
                    res: Res::Param(kind, id),
                    fhir_id: self.next_fhir_id(),
                    span: loc.span,
                };
                let ty = self.desugar_ty(ty);
                let kind = fhir::TyKind::StrgRef(
                    self.mk_lft_hole(),
                    self.genv.alloc(path),
                    self.genv.alloc(ty),
                );
                fhir::Ty { kind, span }
            }
            surface::FnInput::Ty(bind, ty, node_id) => {
                if let Some(bind) = bind
                    && let surface::TyKind::Base(bty) = &ty.kind
                {
                    let bty = self.desugar_bty(bty);
                    let kind =
                        if let Some(idx) = self.implicit_param_into_refine_arg(*bind, *node_id) {
                            fhir::TyKind::Indexed(bty, idx)
                        } else {
                            fhir::TyKind::BaseTy(bty)
                        };
                    fhir::Ty { kind, span: ty.span }
                } else {
                    self.desugar_ty(ty)
                }
            }
        }
    }

    fn desugar_asyncness(
        &mut self,
        asyncness: surface::Async,
        returns: &surface::FnRetTy,
    ) -> fhir::Ty<'genv> {
        match asyncness {
            surface::Async::Yes { span, .. } => {
                // If there's more than one opaque it will fail when collecting it so we can unwrap here
                let def_id = self.opaque.unwrap();

                // FIXME(nilehmann) since we can only pass local ids for opaque types it means we
                // can't support extern specs with opaque types.
                let opaque_ty = self.desugar_opaque_ty_for_async(def_id, returns);
                let opaque_ty = self.insert_opaque_ty(opaque_ty);
                let kind = fhir::TyKind::OpaqueDef(opaque_ty);
                fhir::Ty { kind, span }
            }
            surface::Async::No => self.desugar_fn_ret_ty(returns),
        }
    }

    fn desugar_opaque_ty_for_async(
        &mut self,
        def_id: LocalDefId,
        returns: &surface::FnRetTy,
    ) -> fhir::OpaqueTy<'genv> {
        let output = self.desugar_fn_ret_ty(returns);
        let trait_ref = self.make_lang_item_path(
            hir::LangItem::Future,
            DUMMY_SP,
            &[],
            self.genv.alloc_slice(&[fhir::AssocItemConstraint {
                ident: surface::Ident::with_dummy_span(sym::Output),
                kind: fhir::AssocItemConstraintKind::Equality { term: output },
            }]),
        );
        let bound = fhir::GenericBound::Trait(fhir::PolyTraitRef {
            bound_generic_params: &[],
            refine_params: &[],
            modifiers: fhir::TraitBoundModifier::None,
            trait_ref,
            span: trait_ref.span,
        });
        fhir::OpaqueTy {
            def_id: MaybeExternId::Local(def_id),
            bounds: self.genv.alloc_slice(&[bound]),
        }
    }

    fn make_lang_item_path(
        &mut self,
        lang_item: hir::LangItem,
        span: Span,
        args: &'genv [fhir::GenericArg<'genv>],
        constraints: &'genv [fhir::AssocItemConstraint<'genv>],
    ) -> fhir::Path<'genv> {
        let def_id = self.genv.tcx().require_lang_item(lang_item, span);
        let def_kind = self.genv.def_kind(def_id);
        let res = Res::Def(def_kind, def_id);
        fhir::Path {
            span,
            fhir_id: self.next_fhir_id(),
            res,
            segments: self.genv.alloc_slice_fill_iter([fhir::PathSegment {
                ident: surface::Ident::new(lang_item.name(), span),
                res,
                args,
                constraints,
            }]),
            refine: &[],
        }
    }

    fn desugar_fn_ret_ty(&mut self, returns: &surface::FnRetTy) -> fhir::Ty<'genv> {
        match returns {
            surface::FnRetTy::Ty(ty) => self.desugar_ty(ty),
            surface::FnRetTy::Default(span) => {
                let kind = fhir::TyKind::Tuple(&[]);
                fhir::Ty { kind, span: *span }
            }
        }
    }

    fn desugar_opaque_ty_for_impl_trait(
        &mut self,
        def_id: LocalDefId,
        bounds: &[surface::TraitRef],
    ) -> fhir::OpaqueTy<'genv> {
        let bounds = self.desugar_generic_bounds(bounds);
        fhir::OpaqueTy { def_id: MaybeExternId::Local(def_id), bounds }
    }

    fn desugar_variant_ret(
        &mut self,
        ret: &surface::VariantRet,
    ) -> Result<fhir::VariantRet<'genv>> {
        let Some(enum_id) = self.check_variant_ret_path(&ret.path) else {
            return Err(self.emit(errors::InvalidVariantRet::new(&ret.path)));
        };
        let idx = self.desugar_indices(&ret.indices);
        Ok(fhir::VariantRet { enum_id, idx })
    }

    fn check_variant_ret_path(&mut self, path: &surface::Path) -> Option<DefId> {
        let resolved_id = self.owner.resolved_id();

        match self.resolver_output().path_res_map[&path.node_id].full_res()? {
            fhir::Res::Def(DefKind::Enum, def_id) if def_id == resolved_id => {}
            fhir::Res::SelfTyAlias { .. } => return Some(resolved_id),
            _ => return None,
        }

        let generics = self.genv.tcx().generics_of(resolved_id);
        let args = &path.last().args;
        if generics.own_counts().types != args.len() {
            return None;
        }
        let mut i = 0;
        for param in &generics.own_params {
            let rustc_middle::ty::GenericParamDefKind::Type { .. } = param.kind else { continue };
            let arg = &args[i];
            if let surface::GenericArgKind::Type(arg_ty) = &arg.kind
                && let surface::TyKind::Base(arg_bty) = &arg_ty.kind
                && let surface::BaseTyKind::Path(None, arg_path) = &arg_bty.kind
                && let fhir::Res::Def(DefKind::TyParam, def_id) =
                    self.resolver_output().path_res_map[&arg_path.node_id].full_res()?
                && def_id == param.def_id
            {
            } else {
                return None;
            }
            i += 1;
        }

        Some(resolved_id)
    }

    fn insert_opaque_ty(
        &mut self,
        opaque_ty: fhir::OpaqueTy<'genv>,
    ) -> &'genv fhir::OpaqueTy<'genv> {
        let opaque_ty = self.genv.alloc(opaque_ty);
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item `{:?}`", self.owner))
            .push(opaque_ty);
        opaque_ty
    }
}

impl ErrorEmitter for RustItemCtxt<'_, '_, '_> {
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        self.errors.emit(err)
    }
}

impl ErrorCollector<ErrorGuaranteed> for RustItemCtxt<'_, '_, '_> {
    type Result = std::result::Result<(), ErrorGuaranteed>;

    fn collect(&mut self, err: ErrorGuaranteed) {
        self.errors.collect(err);
    }

    fn into_result(self) -> Self::Result {
        self.errors.into_result()
    }
}

pub(crate) struct FluxItemCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    resolver_output: &'genv ResolverOutput,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: FluxLocalDefId,
    allow_primop_app: bool,
    errors: Errors<'genv>,
}

impl<'genv, 'tcx> FluxItemCtxt<'genv, 'tcx> {
    pub(crate) fn with<T>(
        genv: GlobalEnv<'genv, 'tcx>,
        resolver_output: &'genv ResolverOutput,
        owner: FluxLocalDefId,
        f: impl FnOnce(&mut Self) -> T,
    ) -> Result<T> {
        let mut cx = Self {
            genv,
            resolver_output,
            local_id_gen: Default::default(),
            owner,
            allow_primop_app: false,
            errors: Errors::new(genv.sess()),
        };
        let r = f(&mut cx);
        cx.into_result()?;
        Ok(r)
    }

    pub(crate) fn desugar_flux_item(&mut self, item: &surface::FluxItem) -> fhir::FluxItem<'genv> {
        match item {
            surface::FluxItem::Qualifier(qual) => {
                let qual = self.desugar_qualifier(qual);
                fhir::FluxItem::Qualifier(self.genv.alloc(qual))
            }
            surface::FluxItem::FuncDef(func) => {
                let func = self.desugar_spec_func(func);
                fhir::FluxItem::Func(self.genv.alloc(func))
            }
            surface::FluxItem::PrimOpProp(primop_prop) => {
                self.allow_primop_app = true;
                let primop_prop = self.desugar_primop_prop(primop_prop);
                self.allow_primop_app = false;
                fhir::FluxItem::PrimOpProp(self.genv.alloc(primop_prop))
            }
            surface::FluxItem::SortDecl(sort_decl) => {
                let sort_decl = self.desugar_sort_decl(sort_decl);
                fhir::FluxItem::SortDecl(self.genv.alloc(sort_decl))
            }
        }
    }

    pub(crate) fn desugar_sort_decl(&mut self, sort_decl: &surface::SortDecl) -> fhir::SortDecl {
        fhir::SortDecl {
            def_id: self.owner,
            params: sort_decl.sort_vars.len(),
            span: sort_decl.name.span,
        }
    }

    fn desugar_qualifier(&mut self, qualifier: &surface::Qualifier) -> fhir::Qualifier<'genv> {
        fhir::Qualifier {
            def_id: self.owner,
            args: self.desugar_refine_params(&qualifier.params),
            global: qualifier.global,
            expr: self.desugar_expr(&qualifier.expr),
        }
    }

    fn desugar_primop_prop(
        &mut self,
        primop_prop: &surface::PrimOpProp,
    ) -> fhir::PrimOpProp<'genv> {
        let body = self.desugar_expr(&primop_prop.body);
        let args = self.desugar_refine_params(&primop_prop.params);
        fhir::PrimOpProp {
            def_id: self.owner,
            op: primop_prop.op,
            args,
            body,
            span: primop_prop.span,
        }
    }

    fn desugar_spec_func(&mut self, spec_func: &surface::SpecFunc) -> fhir::SpecFunc<'genv> {
        let body = spec_func.body.as_ref().map(|body| self.desugar_expr(body));
        let params = spec_func.sort_vars.len();
        let sort = self.desugar_sort(&spec_func.output, None);
        let args = self.desugar_refine_params(&spec_func.params);
        let ident_span = spec_func.name.span;
        fhir::SpecFunc {
            def_id: self.owner,
            params,
            args,
            sort,
            body,
            hide: spec_func.hide,
            ident_span,
        }
    }
}

impl ErrorEmitter for FluxItemCtxt<'_, '_> {
    fn emit<'a>(&'a self, err: impl Diagnostic<'a>) -> ErrorGuaranteed {
        self.errors.emit(err)
    }
}

impl ErrorCollector<ErrorGuaranteed> for FluxItemCtxt<'_, '_> {
    type Result = std::result::Result<(), ErrorGuaranteed>;

    fn collect(&mut self, err: ErrorGuaranteed) {
        self.errors.collect(err);
    }

    fn into_result(self) -> Self::Result {
        self.errors.into_result()
    }
}

trait DesugarCtxt<'genv, 'tcx: 'genv>: ErrorEmitter + ErrorCollector<ErrorGuaranteed> {
    fn genv(&self) -> GlobalEnv<'genv, 'tcx>;
    fn resolver_output(&self) -> &'genv ResolverOutput;
    fn next_fhir_id(&self) -> FhirId;
    fn desugar_impl_trait(&mut self, bounds: &[surface::TraitRef]) -> fhir::TyKind<'genv>;

    fn allow_primop_app(&self) -> bool {
        false
    }

    fn resolve_implicit_param(&self, node_id: NodeId) -> Option<(fhir::ParamId, fhir::ParamKind)> {
        self.resolver_output().param_res_map.get(&node_id).copied()
    }

    fn desugar_epath(&self, path: &surface::ExprPath) -> fhir::QPathExpr<'genv> {
        let partial_res = *self
            .resolver_output()
            .expr_path_res_map
            .get(&path.node_id)
            .unwrap_or_else(|| span_bug!(path.span, "unresolved expr path"));

        let unresolved_segments = partial_res.unresolved_segments();

        if unresolved_segments == 0 {
            let path = fhir::PathExpr {
                segments: self
                    .genv()
                    .alloc_slice_fill_iter(path.segments.iter().map(|s| s.ident)),
                res: partial_res.base_res(),
                fhir_id: self.next_fhir_id(),
                span: path.span,
            };
            return fhir::QPathExpr::Resolved(path, None);
        }

        let proj_start = path.segments.len() - unresolved_segments;
        let ty_path = fhir::Path {
            res: partial_res
                .base_res()
                .map_param_id(|_| span_bug!(path.span, "path resolved to refinement parameter")),
            fhir_id: self.next_fhir_id(),
            segments: self.genv().alloc_slice_fill_iter(
                path.segments[..proj_start]
                    .iter()
                    .map(|segment| self.desugar_epath_segment(segment)),
            ),
            refine: &[],
            span: path.span,
        };

        let mut ty = self
            .genv()
            .alloc(self.ty_path(fhir::QPath::Resolved(None, ty_path)));

        for (i, segment) in path.segments.iter().enumerate().skip(proj_start) {
            if i == path.segments.len() - 1 {
                return fhir::QPathExpr::TypeRelative(ty, segment.ident);
            }

            let hir_segment = self.desugar_epath_segment(segment);
            let qpath = fhir::QPath::TypeRelative(ty, self.genv().alloc(hir_segment));
            ty = self.genv().alloc(self.ty_path(qpath));
        }

        span_bug!(
            path.span,
            "desugar_epath: no final extension segment in {}..{}",
            proj_start,
            path.segments.len()
        );
    }

    #[track_caller]
    fn desugar_loc(&self, ident: surface::Ident, node_id: NodeId) -> Result<Res<ParamId>> {
        let partial_res = self.resolver_output().expr_path_res_map[&node_id];
        if let Some(res @ Res::Param(fhir::ParamKind::Loc, _)) = partial_res.full_res() {
            Ok(res)
        } else {
            let span = ident.span;
            Err(self.emit(errors::InvalidLoc { span }))
        }
    }

    #[track_caller]
    fn resolve_param(&self, node_id: NodeId) -> (fhir::ParamId, fhir::ParamKind) {
        self.resolver_output().param_res_map[&node_id]
    }

    fn resolve_implicit_params(
        &self,
        scope: NodeId,
    ) -> impl ExactSizeIterator<Item = (surface::Ident, fhir::ParamId, fhir::ParamKind)> {
        self.resolver_output()
            .implicit_params
            .get(&scope)
            .map_or(&[][..], |it| it)
            .iter()
            .map(|(ident, param_id)| {
                let (param_id, kind) = self.resolve_param(*param_id);
                (*ident, param_id, kind)
            })
    }

    fn implicit_params_to_params(
        &self,
        scope: NodeId,
    ) -> impl ExactSizeIterator<Item = fhir::RefineParam<'genv>> {
        self.resolve_implicit_params(scope)
            .map(|(ident, id, kind)| {
                let sort = if kind.is_loc() { fhir::Sort::Loc } else { fhir::Sort::Infer };
                fhir::RefineParam {
                    id,
                    name: ident.name,
                    span: ident.span,
                    kind,
                    sort,
                    fhir_id: self.next_fhir_id(),
                }
            })
    }

    fn desugar_refine_params(
        &mut self,
        params: &[surface::RefineParam],
    ) -> &'genv [fhir::RefineParam<'genv>] {
        self.genv()
            .alloc_slice_fill_iter(self.desugar_refine_params_iter(params))
    }

    fn desugar_refine_params_iter(
        &mut self,
        params: &[surface::RefineParam],
    ) -> impl ExactSizeIterator<Item = fhir::RefineParam<'genv>> {
        params.iter().map(|param| self.desugar_refine_param(param))
    }

    fn desugar_refine_param(&mut self, param: &surface::RefineParam) -> fhir::RefineParam<'genv> {
        let (id, kind) = self.resolve_param(param.node_id);
        fhir::RefineParam {
            id,
            name: param.ident.name,
            span: param.ident.span,
            kind,
            sort: self.desugar_sort(&param.sort, None),
            fhir_id: self.next_fhir_id(),
        }
    }

    fn desugar_sort(
        &mut self,
        sort: &surface::Sort,
        generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
    ) -> fhir::Sort<'genv> {
        match sort {
            surface::Sort::Base(bsort) => self.desugar_base_sort(bsort, generic_id_to_var_idx),
            surface::Sort::Func { inputs, output } => {
                let inputs_and_output = self.genv().alloc_slice_with_capacity(
                    inputs.len() + 1,
                    inputs
                        .iter()
                        .chain(iter::once(output))
                        .map(|sort| self.desugar_base_sort(sort, generic_id_to_var_idx)),
                );
                fhir::Sort::Func(fhir::PolyFuncSort::new(0, inputs_and_output))
            }
            surface::Sort::Infer => fhir::Sort::Infer,
        }
    }

    fn desugar_base_sort(
        &mut self,
        sort: &surface::BaseSort,
        generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
    ) -> fhir::Sort<'genv> {
        let genv = self.genv();
        match sort {
            surface::BaseSort::BitVec(width) => fhir::Sort::BitVec(*width),
            surface::BaseSort::Path(surface::SortPath { segments, args, node_id }) => {
                let res = self.resolver_output().sort_path_res_map[node_id];

                // In a `RefinedBy` we resolve type parameters to a sort var
                let res = if let fhir::SortRes::TyParam(def_id) = res
                    && let Some(generic_id_to_var_idx) = generic_id_to_var_idx
                {
                    let idx = generic_id_to_var_idx.get_index_of(&def_id).unwrap();
                    fhir::SortRes::SortParam(idx)
                } else {
                    res
                };

                let args = genv.alloc_slice_fill_iter(
                    args.iter()
                        .map(|s| self.desugar_base_sort(s, generic_id_to_var_idx)),
                );

                let path = fhir::SortPath { res, segments: genv.alloc_slice(segments), args };
                fhir::Sort::Path(path)
            }
            surface::BaseSort::SortOf(qself, path) => {
                fhir::Sort::SortOf(self.desugar_path_to_bty(Some(qself), path))
            }
        }
    }

    fn desugar_generic_args(
        &mut self,
        res: Res,
        args: &[surface::GenericArg],
    ) -> (&'genv [fhir::GenericArg<'genv>], &'genv [fhir::AssocItemConstraint<'genv>]) {
        let mut fhir_args = vec![];
        let mut constraints = vec![];
        if let Res::Def(
            DefKind::TyAlias | DefKind::Struct | DefKind::Enum | DefKind::OpaqueTy,
            def_id,
        ) = res
        {
            let generics = self.genv().tcx().generics_of(def_id);
            for param in &generics.own_params {
                if let rustc_middle::ty::GenericParamDefKind::Lifetime = param.kind {
                    fhir_args.push(fhir::GenericArg::Lifetime(self.mk_lft_hole()));
                }
            }
        }
        for arg in args {
            match &arg.kind {
                surface::GenericArgKind::Type(ty) => {
                    if matches!(ty.kind, surface::TyKind::Hole) {
                        fhir_args.push(fhir::GenericArg::Infer);
                        continue;
                    }
                    // If the path was resolved in the value namespace then we must create a const
                    // generic argument
                    if let Some(path) = ty.is_potential_const_arg()
                        && let Some(res) =
                            self.resolver_output().path_res_map[&path.node_id].full_res()
                        && res.matches_ns(Namespace::ValueNS)
                    {
                        fhir_args.push(self.desugar_const_path_to_const_arg(path, res));
                        continue;
                    }
                    let ty = self.desugar_ty(ty);
                    fhir_args.push(fhir::GenericArg::Type(self.genv().alloc(ty)));
                }
                surface::GenericArgKind::Constraint(ident, ty) => {
                    constraints.push(fhir::AssocItemConstraint {
                        ident: *ident,
                        kind: fhir::AssocItemConstraintKind::Equality { term: self.desugar_ty(ty) },
                    });
                }
            }
        }
        (self.genv().alloc_slice(&fhir_args), self.genv().alloc_slice(&constraints))
    }

    fn desugar_const_path_to_const_arg(
        &mut self,
        path: &surface::Path,
        res: fhir::Res<!>,
    ) -> fhir::GenericArg<'genv> {
        let kind = if let Res::Def(DefKind::ConstParam, def_id) = res {
            fhir::ConstArgKind::Param(def_id)
        } else {
            self.emit(errors::UnsupportedConstGenericArg::new(path.span, res.descr()));
            fhir::ConstArgKind::Infer
        };
        fhir::GenericArg::Const(fhir::ConstArg { kind, span: path.span })
    }

    /// This is the mega desugaring function [`surface::Ty`] -> [`fhir::Ty`].
    /// These are both similar representations. The most important difference is that
    /// [`fhir::Ty`] has explicit refinement parameters and [`surface::Ty`] does not.
    /// Refinements are implicitly scoped in surface.
    fn desugar_ty(&mut self, ty: &surface::Ty) -> fhir::Ty<'genv> {
        let node_id = ty.node_id;
        let span = ty.span;
        let kind = match &ty.kind {
            surface::TyKind::Base(bty) => {
                let bty = self.desugar_bty(bty);
                fhir::TyKind::BaseTy(bty)
            }
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.desugar_bty(bty);
                let idx = self.desugar_indices(indices);
                fhir::TyKind::Indexed(bty, idx)
            }
            surface::TyKind::Exists { bind, bty, pred } => {
                let ty_span = ty.span;
                let bty_span = bty.span;

                let bty = self.desugar_bty(bty);
                let pred = self.desugar_expr(pred);

                let (id, kind) = self.resolve_param(node_id);
                let param = fhir::RefineParam {
                    id,
                    name: bind.name,
                    span: bind.span,
                    sort: fhir::Sort::Infer,
                    kind,
                    fhir_id: self.next_fhir_id(),
                };
                let path = fhir::PathExpr {
                    segments: self.genv().alloc_slice(&[*bind]),
                    res: Res::Param(kind, id),
                    fhir_id: self.next_fhir_id(),
                    span: bind.span,
                };
                let idx = fhir::Expr {
                    kind: fhir::ExprKind::Var(QPathExpr::Resolved(path, None)),
                    span: bind.span,
                    fhir_id: self.next_fhir_id(),
                };
                let indexed = fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: bty_span };
                let constr = fhir::Ty {
                    kind: fhir::TyKind::Constr(pred, self.genv().alloc(indexed)),
                    span: ty_span,
                };
                fhir::TyKind::Exists(self.genv().alloc_slice(&[param]), self.genv().alloc(constr))
            }
            surface::TyKind::GeneralExists { params, ty, pred } => {
                let mut ty = self.desugar_ty(ty);
                if let Some(pred) = pred {
                    let pred = self.desugar_expr(pred);
                    ty = fhir::Ty { kind: fhir::TyKind::Constr(pred, self.genv().alloc(ty)), span };
                }
                let params = self.desugar_refine_params(params);

                fhir::TyKind::Exists(params, self.genv().alloc(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.desugar_expr(pred);
                let ty = self.desugar_ty(ty);
                fhir::TyKind::Constr(pred, self.genv().alloc(ty))
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let ty = self.desugar_ty(ty);
                let mut_ty = fhir::MutTy { ty: self.genv().alloc(ty), mutbl: *mutbl };
                fhir::TyKind::Ref(self.mk_lft_hole(), mut_ty)
            }
            surface::TyKind::Tuple(tys) => {
                let tys = self
                    .genv()
                    .alloc_slice_fill_iter(tys.iter().map(|ty| self.desugar_ty(ty)));
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(ty);
                let len = Self::desugar_const_arg(len);
                fhir::TyKind::Array(self.genv().alloc(ty), len)
            }
            surface::TyKind::ImplTrait(_, bounds) => self.desugar_impl_trait(bounds),
            surface::TyKind::Hole => fhir::TyKind::Infer,
        };
        fhir::Ty { kind, span }
    }

    fn desugar_const_arg(const_arg: &surface::ConstArg) -> fhir::ConstArg {
        let kind = match const_arg.kind {
            surface::ConstArgKind::Lit(val) => fhir::ConstArgKind::Lit(val),
            surface::ConstArgKind::Infer => fhir::ConstArgKind::Infer,
        };
        fhir::ConstArg { kind, span: const_arg.span }
    }

    fn desugar_bty(&mut self, bty: &surface::BaseTy) -> fhir::BaseTy<'genv> {
        match &bty.kind {
            surface::BaseTyKind::Path(qself, path) => {
                let qpath = self.desugar_qpath(qself.as_deref(), path);
                fhir::BaseTy::from_qpath(qpath, self.next_fhir_id())
            }
            surface::BaseTyKind::Slice(ty) => {
                let ty = self.desugar_ty(ty);
                let kind = fhir::BaseTyKind::Slice(self.genv().alloc(ty));
                fhir::BaseTy { kind, fhir_id: self.next_fhir_id(), span: bty.span }
            }
        }
    }

    fn desugar_path_to_bty(
        &mut self,
        qself: Option<&surface::Ty>,
        path: &surface::Path,
    ) -> fhir::BaseTy<'genv> {
        let qpath = self.desugar_qpath(qself, path);
        fhir::BaseTy::from_qpath(qpath, self.next_fhir_id())
    }

    fn desugar_qpath(
        &mut self,
        qself: Option<&surface::Ty>,
        path: &surface::Path,
    ) -> fhir::QPath<'genv> {
        let qself = if let Some(ty) = qself {
            let ty = self.desugar_ty(ty);
            Some(self.genv().alloc(ty))
        } else {
            None
        };
        let partial_res = self.resolver_output().path_res_map[&path.node_id];

        let unresolved_segments = partial_res.unresolved_segments();

        let proj_start = path.segments.len() - unresolved_segments;
        let fhir_path = fhir::Path {
            res: partial_res.base_res(),
            fhir_id: self.next_fhir_id(),
            segments: self.genv().alloc_slice_fill_iter(
                path.segments[..proj_start]
                    .iter()
                    .map(|segment| self.desugar_path_segment(segment)),
            ),
            refine: self
                .genv()
                .alloc_slice_fill_iter(path.refine.iter().map(|arg| self.desugar_refine_arg(arg))),
            span: path.span,
        };

        // Simple case, either no projections, or only fully-qualified.
        // E.g., `std::mem::size_of` or `<I as Iterator>::Item`.
        if unresolved_segments == 0 {
            return fhir::QPath::Resolved(qself, fhir_path);
        }

        // Create the innermost type that we're projecting from.
        let mut ty = if fhir_path.segments.is_empty() {
            // If the base path is empty that means there exists a
            // syntactical `Self`, e.g., `&i32` in `<&i32>::clone`.
            qself.expect("missing QSelf for <T>::...")
        } else {
            // Otherwise, the base path is an implicit `Self` type path,
            // e.g., `Vec` in `Vec::new` or `<I as Iterator>::Item` in
            // `<I as Iterator>::Item::default`.
            self.genv()
                .alloc(self.ty_path(fhir::QPath::Resolved(qself, fhir_path)))
        };

        for (i, segment) in path.segments.iter().enumerate().skip(proj_start) {
            let hir_segment = self.desugar_path_segment(segment);
            let qpath = fhir::QPath::TypeRelative(ty, self.genv().alloc(hir_segment));

            if i == path.segments.len() - 1 {
                return qpath;
            }

            ty = self.genv().alloc(self.ty_path(qpath));
        }

        span_bug!(
            path.span,
            "desugar_qpath: no final extension segment in {}..{}",
            proj_start,
            path.segments.len()
        );
    }

    fn desugar_path_segment(&mut self, segment: &surface::PathSegment) -> fhir::PathSegment<'genv> {
        let res = self
            .resolver_output()
            .path_res_map
            .get(&segment.node_id)
            .map_or(Res::Err, |r| r.expect_full_res());
        let (args, constraints) = self.desugar_generic_args(res, &segment.args);
        fhir::PathSegment { ident: segment.ident, res, args, constraints }
    }

    fn desugar_epath_segment(
        &self,
        segment: &surface::ExprPathSegment,
    ) -> fhir::PathSegment<'genv> {
        let res = self
            .resolver_output()
            .expr_path_res_map
            .get(&segment.node_id)
            .map_or(Res::Err, |r| r.expect_full_res())
            .map_param_id(|_| bug!("segment resolved to refinement parameter"));
        fhir::PathSegment { ident: segment.ident, res, args: &[], constraints: &[] }
    }

    fn ty_path(&self, qpath: fhir::QPath<'genv>) -> fhir::Ty<'genv> {
        fhir::Ty {
            span: qpath.span(),
            kind: fhir::TyKind::BaseTy(fhir::BaseTy::from_qpath(qpath, self.next_fhir_id())),
        }
    }

    fn mk_lft_hole(&self) -> fhir::Lifetime {
        fhir::Lifetime::Hole(self.next_fhir_id())
    }

    fn desugar_indices(&mut self, idxs: &surface::Indices) -> fhir::Expr<'genv> {
        if let [arg] = &idxs.indices[..] {
            self.desugar_refine_arg(arg)
        } else {
            let flds = self
                .genv()
                .alloc_slice_fill_iter(idxs.indices.iter().map(|arg| self.desugar_refine_arg(arg)));
            fhir::Expr {
                kind: fhir::ExprKind::Record(flds),
                fhir_id: self.next_fhir_id(),
                span: idxs.span,
            }
        }
    }

    fn desugar_refine_arg(&mut self, arg: &surface::RefineArg) -> fhir::Expr<'genv> {
        match arg {
            surface::RefineArg::Bind(ident, .., node_id) => {
                self.implicit_param_into_refine_arg(*ident, *node_id)
                    .unwrap()
            }
            surface::RefineArg::Expr(expr) => self.desugar_expr(expr),
            surface::RefineArg::Abs(params, body, span, _) => {
                let body = self.genv().alloc(self.desugar_expr(body));
                let params = self.desugar_refine_params(params);
                fhir::Expr {
                    kind: fhir::ExprKind::Abs(params, body),
                    fhir_id: self.next_fhir_id(),
                    span: *span,
                }
            }
        }
    }

    fn implicit_param_into_refine_arg(
        &self,
        ident: surface::Ident,
        node_id: NodeId,
    ) -> Option<fhir::Expr<'genv>> {
        let (id, kind) = self.resolve_implicit_param(node_id)?;
        let path = fhir::PathExpr {
            segments: self.genv().alloc_slice(&[ident]),
            res: Res::Param(kind, id),
            fhir_id: self.next_fhir_id(),
            span: ident.span,
        };
        Some(fhir::Expr {
            kind: fhir::ExprKind::Var(QPathExpr::Resolved(path, Some(kind))),
            span: ident.span,
            fhir_id: self.next_fhir_id(),
        })
    }

    fn desugar_expr(&mut self, expr: &surface::Expr) -> fhir::Expr<'genv> {
        let kind = match &expr.kind {
            surface::ExprKind::Path(path) => fhir::ExprKind::Var(self.desugar_epath(path)),
            surface::ExprKind::Literal(lit) => self.desugar_lit(expr.span, *lit),
            surface::ExprKind::BinaryOp(op, box [e1, e2]) => {
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::BinaryOp(*op, self.genv().alloc(e1), self.genv().alloc(e2))
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(*op, self.genv().alloc(self.desugar_expr(e)))
            }
            surface::ExprKind::Dot(base, fld) => {
                let base = self.desugar_expr(base);
                fhir::ExprKind::Dot(self.genv().alloc(base), *fld)
            }
            surface::ExprKind::Call(callee, args) => self.desugar_call(callee, args),
            surface::ExprKind::AssocReft(..) | surface::ExprKind::PrimUIF(..) => {
                fhir::ExprKind::Err(self.emit(errors::UnsupportedPosition::new(expr.span)))
            }
            surface::ExprKind::IfThenElse(box [p, e1, e2]) => {
                let p = self.desugar_expr(p);
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::IfThenElse(
                    self.genv().alloc(p),
                    self.genv().alloc(e1),
                    self.genv().alloc(e2),
                )
            }
            surface::ExprKind::Constructor(path, args) => {
                self.desugar_constructor(path.as_ref(), args)
            }
            surface::ExprKind::BoundedQuant(kind, param, rng, body) => {
                let kind = match kind {
                    surface::QuantKind::Exists => fhir::QuantKind::Exists,
                    surface::QuantKind::Forall => fhir::QuantKind::Forall,
                };
                let body = self.genv().alloc(self.desugar_expr(body));
                let param = self.desugar_refine_param(param);
                let rng = fhir::Range { start: rng.start, end: rng.end };
                fhir::ExprKind::BoundedQuant(kind, param, rng, body)
            }
            surface::ExprKind::Block(decls, body) => {
                let decls = self.genv().alloc_slice_fill_iter(decls.iter().map(|decl| {
                    fhir::LetDecl {
                        param: self.desugar_refine_param(&decl.param),
                        init: self.desugar_expr(&decl.init),
                    }
                }));
                let body = self.genv().alloc(self.desugar_expr(body));
                fhir::ExprKind::Block(decls, body)
            }
            surface::ExprKind::SetLiteral(exprs) => {
                let exprs = self
                    .genv()
                    .alloc_slice_fill_iter(exprs.iter().map(|expr| self.desugar_expr(expr)));
                fhir::ExprKind::SetLiteral(exprs)
            }
        };

        fhir::Expr { kind, span: expr.span, fhir_id: self.next_fhir_id() }
    }

    fn desugar_call(
        &mut self,
        callee: &surface::Expr,
        args: &[surface::Expr],
    ) -> fhir::ExprKind<'genv> {
        let args = self.desugar_exprs(args);
        match &callee.kind {
            surface::ExprKind::Path(path) => {
                match self.desugar_epath(path) {
                    QPathExpr::Resolved(path, _) => fhir::ExprKind::App(path, args),
                    QPathExpr::TypeRelative(qself, name) => {
                        fhir::ExprKind::Alias(fhir::AliasReft::TypeRelative { qself, name }, args)
                    }
                }
            }
            surface::ExprKind::PrimUIF(op) if args.len() == 2 && self.allow_primop_app() => {
                fhir::ExprKind::PrimApp(*op, &args[0], &args[1])
            }
            surface::ExprKind::AssocReft(qself, path, name) => {
                let qself = self.desugar_ty(qself);
                let fhir::QPath::Resolved(None, trait_) = self.desugar_qpath(None, path) else {
                    span_bug!(path.span, "desugar_alias_reft: unexpected qpath")
                };
                let Res::Def(DefKind::Trait, _) = trait_.res else {
                    // FIXME(nilehmann) we ought to report this error somewhere else
                    return fhir::ExprKind::Err(self.emit(errors::InvalidAliasReft::new(path)));
                };
                let alias_reft = fhir::AliasReft::Qualified {
                    qself: self.genv().alloc(qself),
                    trait_,
                    name: *name,
                };
                fhir::ExprKind::Alias(alias_reft, args)
            }
            _ => fhir::ExprKind::Err(self.emit(errors::UnsupportedPosition::new(callee.span))),
        }
    }

    fn desugar_constructor(
        &mut self,
        path: Option<&surface::ExprPath>,
        args: &[surface::ConstructorArg],
    ) -> fhir::ExprKind<'genv> {
        let path = if let Some(path) = path {
            let Some(res @ Res::Def(DefKind::Struct | DefKind::Enum, _)) =
                self.resolver_output().expr_path_res_map[&path.node_id].full_res()
            else {
                return fhir::ExprKind::Err(
                    self.emit(errors::InvalidConstructorPath { span: path.span }),
                );
            };
            let segments = self
                .genv()
                .alloc_slice_fill_iter(path.segments.iter().map(|s| s.ident));
            Some(fhir::PathExpr { res, segments, fhir_id: self.next_fhir_id(), span: path.span })
        } else {
            None
        };

        let (field_exprs, spreads): (Vec<_>, Vec<_>) = args.iter().partition_map(|arg| {
            match arg {
                ConstructorArg::FieldExpr(e) => Either::Left(e),
                ConstructorArg::Spread(s) => Either::Right(s),
            }
        });

        let field_exprs = self
            .genv()
            .alloc_slice_fill_iter(field_exprs.iter().map(|field_expr| {
                let e = self.desugar_expr(&field_expr.expr);
                fhir::FieldExpr {
                    ident: field_expr.ident,
                    expr: e,
                    fhir_id: self.next_fhir_id(),
                    span: e.span,
                }
            }));

        match &spreads[..] {
            [] => fhir::ExprKind::Constructor(path, field_exprs, None),
            [s] => {
                let spread = fhir::Spread {
                    expr: self.desugar_expr(&s.expr),
                    span: s.span,
                    fhir_id: self.next_fhir_id(),
                };
                fhir::ExprKind::Constructor(path, field_exprs, Some(self.genv().alloc(spread)))
            }
            [s1, s2, ..] => {
                let err = errors::MultipleSpreadsInConstructor::new(s1.span, s2.span);
                fhir::ExprKind::Err(self.emit(err))
            }
        }
    }

    fn desugar_exprs(&mut self, exprs: &[surface::Expr]) -> &'genv [fhir::Expr<'genv>] {
        self.genv()
            .alloc_slice_fill_iter(exprs.iter().map(|e| self.desugar_expr(e)))
    }

    fn try_parse_int_lit(&self, span: Span, s: &str) -> Result<u128> {
        let s = s.replace("_", "");
        let parsed_int = if s.len() <= 2 {
            s.parse::<u128>()
        } else {
            match &s[0..2] {
                "0x" => u128::from_str_radix(&s[2..], 16), // hex
                "0o" => u128::from_str_radix(&s[2..], 8),  // octal
                "0b" => u128::from_str_radix(&s[2..], 2),  // binary
                _ => s.parse::<u128>(),                    // must be decimal
            }
        };

        if let Ok(n) = parsed_int {
            Ok(n) // convert error types
        } else {
            Err(self.emit(errors::IntTooLarge { span }))
        }
    }

    /// Desugar surface literal
    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> fhir::ExprKind<'genv> {
        let lit = match lit.kind {
            surface::LitKind::Integer => {
                let n = match self.try_parse_int_lit(span, lit.symbol.as_str()) {
                    Ok(n) => n,
                    Err(err) => return fhir::ExprKind::Err(err),
                };
                match lit.suffix {
                    Some(sym::int) => fhir::Lit::Int(n, Some(fhir::NumLitKind::Int)),
                    Some(sym::real) => fhir::Lit::Int(n, Some(fhir::NumLitKind::Real)),
                    None => fhir::Lit::Int(n, None),
                    Some(suffix) => {
                        return fhir::ExprKind::Err(
                            self.emit(errors::InvalidNumericSuffix::new(span, suffix)),
                        );
                    }
                }
            }
            surface::LitKind::Bool => fhir::Lit::Bool(lit.symbol == kw::True),
            surface::LitKind::Str => fhir::Lit::Str(lit.symbol),
            surface::LitKind::Char => fhir::Lit::Char(lit.symbol.as_str().parse::<char>().unwrap()),
            _ => return fhir::ExprKind::Err(self.emit(errors::UnexpectedLiteral { span })),
        };
        fhir::ExprKind::Literal(lit)
    }
}

impl<'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for RustItemCtxt<'_, 'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId {
            owner: FluxOwnerId::Rust(self.owner.local_id()),
            local_id: self.local_id_gen.fresh(),
        }
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &'genv ResolverOutput {
        self.resolver_output
    }

    fn desugar_impl_trait(&mut self, bounds: &[surface::TraitRef]) -> fhir::TyKind<'genv> {
        // If there's more than one opaque it will fail when collecting it so we can unwrap here
        let def_id = self.opaque.unwrap();

        // FIXME(nilehmann) since we can only pass local ids for opaque types it means we can't
        // support extern specs with opaque types.
        let opaque_ty = self.desugar_opaque_ty_for_impl_trait(def_id, bounds);
        let opaque_ty = self.insert_opaque_ty(opaque_ty);

        fhir::TyKind::OpaqueDef(opaque_ty)
    }
}

impl<'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for FluxItemCtxt<'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Flux(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn allow_primop_app(&self) -> bool {
        self.allow_primop_app
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &'genv ResolverOutput {
        self.resolver_output
    }

    fn desugar_impl_trait(&mut self, _: &[surface::TraitRef]) -> fhir::TyKind<'genv> {
        unimplemented!("`impl Trait` not supported in this item")
    }
}

/// Traverses the `hir` for an item and collects the `def_id` of any opaque type (i.e., `impl Trait` or `async`)
/// Currently, we only support up to one opaque type and we report an error if there's more than one.
fn collect_opaque_types(
    genv: GlobalEnv,
    owner_id: MaybeExternId<OwnerId>,
) -> Result<Option<LocalDefId>> {
    let mut collector = OpaqueTypeCollector::new(genv.sess());
    match genv.tcx().hir_owner_node(owner_id.local_id()) {
        hir::OwnerNode::Item(item) => hir::intravisit::walk_item(&mut collector, item),
        hir::OwnerNode::ImplItem(impl_item) => {
            hir::intravisit::walk_impl_item(&mut collector, impl_item);
        }
        hir::OwnerNode::TraitItem(trait_item) => {
            hir::intravisit::walk_trait_item(&mut collector, trait_item);
        }
        hir::OwnerNode::ForeignItem(_) | hir::OwnerNode::Crate(_) | hir::OwnerNode::Synthetic => {}
    };
    collector.into_result()
}

struct OpaqueTypeCollector<'sess> {
    opaque: Option<LocalDefId>,
    errors: Errors<'sess>,
}

impl<'sess> OpaqueTypeCollector<'sess> {
    fn new(sess: &'sess FluxSession) -> Self {
        Self { opaque: None, errors: Errors::new(sess) }
    }

    fn into_result(self) -> Result<Option<LocalDefId>> {
        self.errors.into_result()?;
        Ok(self.opaque)
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for OpaqueTypeCollector<'_> {
    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx, rustc_hir::AmbigArg>) {
        if let hir::TyKind::OpaqueDef(opaque_ty, ..) = ty.kind {
            if self.opaque.is_some() {
                self.errors.emit(errors::UnsupportedSignature {
                    span: ty.span,
                    note: "duplicate opaque types in signature",
                });
            } else {
                self.opaque = Some(opaque_ty.def_id);
            }
        }
        hir::intravisit::walk_ty(self, ty);
    }
}
