//! "Lift" HIR types into  FHIR types.
//!
use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use hir::{def::DefKind, OwnerId};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{middle::resolve_bound_vars::ResolvedArg, ty::TyCtxt};

use super::{FhirId, FluxOwnerId};
use crate::fhir;

pub struct LiftCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
    local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
}

pub fn lift_refined_by(tcx: TyCtxt, owner_id: OwnerId) -> fhir::RefinedBy {
    let def_id = owner_id.def_id;
    let item = tcx.hir().expect_item(def_id);
    match item.kind {
        hir::ItemKind::TyAlias(..) | hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => {
            fhir::RefinedBy::new(def_id, [], [], item.ident.span)
        }
        _ => {
            bug!("expected struct, enum or type alias");
        }
    }
}

pub fn lift_type_alias(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<(fhir::Generics, fhir::GenericPredicates, fhir::TyAlias), ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    let item = tcx.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(ty, hir_generics) = item.kind else {
        bug!("expected type alias");
    };
    let local_id_gen = IndexGen::new();
    let mut cx = LiftCtxt::new(tcx, sess, owner_id, &local_id_gen, None);

    let generics = cx.lift_generics_inner(hir_generics)?;
    let predicates = cx.lift_generic_predicates(hir_generics)?;
    let ty = cx.lift_ty(ty)?;
    let ty_alias = fhir::TyAlias {
        owner_id,
        early_bound_params: vec![],
        index_params: vec![],
        ty,
        span: item.span,
        lifted: true,
    };

    Ok((generics, predicates, ty_alias))
}

pub fn lift_fn(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<(fhir::Generics, fhir::FnInfo), ErrorGuaranteed> {
    let mut opaque_tys = Default::default();
    let local_id_gen = IndexGen::new();
    let mut cx = LiftCtxt::new(tcx, sess, owner_id, &local_id_gen, Some(&mut opaque_tys));

    let def_id = owner_id.def_id;
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);

    let hir_generics = tcx.hir().get_generics(def_id).unwrap();
    let fn_sig = tcx
        .hir()
        .fn_sig_by_hir_id(hir_id)
        .expect("item does not have a `FnDecl`");

    let generics = cx.lift_generics_inner(hir_generics)?;
    let fn_sig = cx.lift_fn_sig(fn_sig)?;
    let fn_preds = cx.lift_generic_predicates(hir_generics)?;

    Ok((generics, fhir::FnInfo { fn_sig, predicates: fn_preds, opaque_tys }))
}

/// HACK(nilehmann) this is used during annot check to allow an explicit type to refine [`Self`].
/// For example, in `impl List<T> { fn foo(&self) }` the type of `self` is `&Self` and we want to
/// allow a refinement using `&List<T>`.
/// Do not use this outside of annot check because the `FhirId`s will be wrong.
///
/// [`Self`]: fhir::Res::SelfTyAlias
pub fn lift_self_ty(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<Option<fhir::Ty>, ErrorGuaranteed> {
    if let Some(def_id) = tcx.impl_of_method(owner_id.to_def_id()) {
        let owner_id = OwnerId { def_id: def_id.expect_local() };
        let local_id_gen = IndexGen::new();
        let mut cx = LiftCtxt::new(tcx, sess, owner_id, &local_id_gen, None);
        let local_id = def_id.expect_local();
        let hir::Item { kind: hir::ItemKind::Impl(impl_), .. } = tcx.hir().expect_item(local_id)
        else {
            bug!("expected an impl")
        };
        let self_ty = cx.lift_ty(impl_.self_ty)?;
        Ok(Some(self_ty))
    } else if let def_kind @ (DefKind::Struct | DefKind::Enum) = tcx.def_kind(owner_id) {
        let generics = tcx.hir().get_generics(owner_id.def_id).unwrap();
        let item = tcx.hir().expect_item(owner_id.def_id);
        let local_id_gen = IndexGen::new();
        let cx = LiftCtxt::new(tcx, sess, owner_id, &local_id_gen, None);

        let span = item.ident.span.to(generics.span);
        let path = fhir::Path {
            res: fhir::Res::Def(def_kind, owner_id.to_def_id()),
            args: cx.generic_params_into_args(generics)?,
            bindings: vec![],
            refine: vec![],
            span,
        };
        let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
        Ok(Some(fhir::Ty { fhir_id: cx.next_fhir_id(), span, kind: fhir::TyKind::BaseTy(bty) }))
    } else {
        Ok(None)
    }
}

impl<'a, 'tcx> LiftCtxt<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        owner: OwnerId,
        local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy>>,
    ) -> Self {
        Self { tcx, sess, opaque_tys, local_id_gen, owner }
    }

    fn with_new_owner<'b>(&'b mut self, owner: OwnerId) -> LiftCtxt<'b, 'tcx> {
        LiftCtxt::new(self.tcx, self.sess, owner, self.local_id_gen, self.opaque_tys.as_deref_mut())
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
    }

    pub fn lift_generics_with_predicates(
        &mut self,
    ) -> Result<(fhir::Generics, fhir::GenericPredicates), ErrorGuaranteed> {
        let generics = self.tcx.hir().get_generics(self.owner.def_id).unwrap();
        Ok((self.lift_generics_inner(generics)?, self.lift_generic_predicates(generics)?))
    }

    pub fn lift_generics(&mut self) -> Result<fhir::Generics, ErrorGuaranteed> {
        let generics = self.tcx.hir().get_generics(self.owner.def_id).unwrap();
        self.lift_generics_inner(generics)
    }

    fn lift_generic_param(
        &mut self,
        param: &hir::GenericParam,
    ) -> Result<fhir::GenericParam, ErrorGuaranteed> {
        let kind = match param.kind {
            hir::GenericParamKind::Lifetime { .. } => fhir::GenericParamKind::Lifetime,
            hir::GenericParamKind::Type { default, synthetic: false } => {
                fhir::GenericParamKind::Type {
                    default: default.map(|ty| self.lift_ty(ty)).transpose()?,
                }
            }
            hir::GenericParamKind::Type { synthetic: true, .. } => {
                return self.emit_err(errors::UnsupportedHir::new(
                    self.tcx,
                    param.def_id,
                    "`impl Trait` in argument position not supported",
                ))
            }
            hir::GenericParamKind::Const { .. } => {
                return self.emit_err(errors::UnsupportedHir::new(
                    self.tcx,
                    param.def_id,
                    "const generics are not supported",
                ))
            }
        };
        Ok(fhir::GenericParam { def_id: param.def_id, kind })
    }

    fn lift_generics_inner(
        &mut self,
        generics: &hir::Generics,
    ) -> Result<fhir::Generics, ErrorGuaranteed> {
        let params = generics
            .params
            .iter()
            .map(|param| self.lift_generic_param(param))
            .try_collect_exhaust()?;
        Ok(fhir::Generics { params })
    }

    pub fn lift_generic_predicates(
        &mut self,
        generics: &hir::Generics,
    ) -> Result<fhir::GenericPredicates, ErrorGuaranteed> {
        let predicates = generics
            .predicates
            .iter()
            .map(|pred| self.lift_where_predicate(pred))
            .try_collect_exhaust()?;
        Ok(fhir::GenericPredicates { predicates })
    }

    fn lift_where_predicate(
        &mut self,
        pred: &hir::WherePredicate,
    ) -> Result<fhir::WhereBoundPredicate, ErrorGuaranteed> {
        if let hir::WherePredicate::BoundPredicate(bound) = pred {
            if !bound.bound_generic_params.is_empty() {
                return self.emit_unsupported("higher-rank trait bounds are not supported 3");
            }
            let bounded_ty = self.lift_ty(bound.bounded_ty)?;
            let bounds = bound
                .bounds
                .iter()
                .map(|bound| self.lift_generic_bound(bound))
                .try_collect()?;

            Ok(fhir::WhereBoundPredicate { bounded_ty, bounds, span: bound.span })
        } else {
            self.emit_unsupported(&format!("unsupported where predicate: `{pred:?}`"))
        }
    }

    fn lift_generic_bound(
        &mut self,
        bound: &hir::GenericBound,
    ) -> Result<fhir::GenericBound, ErrorGuaranteed> {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref, hir::TraitBoundModifier::None) => {
                Ok(fhir::GenericBound::Trait(
                    self.lift_poly_trait_ref(*poly_trait_ref)?,
                    fhir::TraitBoundModifier::None,
                ))
            }
            hir::GenericBound::Trait(poly_trait_ref, hir::TraitBoundModifier::Maybe) => {
                Ok(fhir::GenericBound::Trait(
                    self.lift_poly_trait_ref(*poly_trait_ref)?,
                    fhir::TraitBoundModifier::Maybe,
                ))
            }
            hir::GenericBound::LangItemTrait(lang_item, .., args) => {
                Ok(fhir::GenericBound::LangItemTrait(
                    *lang_item,
                    self.lift_generic_args(args.args)?,
                    self.lift_type_bindings(args.bindings)?,
                ))
            }
            _ => self.emit_unsupported(&format!("unsupported generic bound: `{bound:?}`")),
        }
    }

    fn lift_poly_trait_ref(
        &mut self,
        poly_trait_ref: hir::PolyTraitRef,
    ) -> Result<fhir::PolyTraitRef, ErrorGuaranteed> {
        let bound_generic_params = poly_trait_ref
            .bound_generic_params
            .iter()
            .map(|param| self.lift_generic_param(param))
            .try_collect_exhaust()?;
        Ok(fhir::PolyTraitRef {
            bound_generic_params,
            trait_ref: self.lift_path(poly_trait_ref.trait_ref.path)?,
        })
    }

    fn lift_opaque_ty(&mut self, item_id: hir::ItemId) -> Result<fhir::OpaqueTy, ErrorGuaranteed> {
        let hir::ItemKind::OpaqueTy(opaque_ty) = self.tcx.hir().item(item_id).kind else {
            bug!("expected opaque type")
        };

        let opaque_ty = fhir::OpaqueTy {
            bounds: opaque_ty
                .bounds
                .iter()
                .map(|bound| self.lift_generic_bound(bound))
                .try_collect()?,
        };
        Ok(opaque_ty)
    }

    fn lift_fn_sig(&mut self, fn_sig: &hir::FnSig) -> Result<fhir::FnSig, ErrorGuaranteed> {
        let args = fn_sig
            .decl
            .inputs
            .iter()
            .map(|ty| self.lift_ty(ty))
            .try_collect_exhaust()?;

        let output = fhir::FnOutput {
            params: vec![],
            ensures: vec![],
            ret: self.lift_fn_ret_ty(&fn_sig.decl.output)?,
        };

        let fn_sig = fhir::FnSig {
            params: vec![],
            requires: vec![],
            args,
            output,
            lifted: true,
            span: fn_sig.span,
        };
        Ok(fn_sig)
    }

    fn lift_fn_ret_ty(&mut self, ret_ty: &hir::FnRetTy) -> Result<fhir::Ty, ErrorGuaranteed> {
        match ret_ty {
            hir::FnRetTy::DefaultReturn(_) => {
                let kind = fhir::TyKind::Tuple(vec![]);
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span: ret_ty.span() })
            }
            hir::FnRetTy::Return(ty) => self.lift_ty(ty),
        }
    }

    pub fn lift_field_def_id(
        &mut self,
        def_id: LocalDefId,
    ) -> Result<fhir::FieldDef, ErrorGuaranteed> {
        let hir = self.tcx.hir();
        let hir_id = hir.local_def_id_to_hir_id(def_id);
        let hir::Node::Field(field_def) = hir.get(hir_id) else { bug!("expected a field") };
        Ok(fhir::FieldDef { def_id, ty: self.lift_ty(field_def.ty)?, lifted: true })
    }

    pub fn lift_field_def(
        &mut self,
        field_def: &hir::FieldDef,
    ) -> Result<fhir::FieldDef, ErrorGuaranteed> {
        let ty = self.lift_ty(field_def.ty)?;
        Ok(fhir::FieldDef { def_id: field_def.def_id, ty, lifted: true })
    }

    pub fn lift_enum_variant_id(
        &mut self,
        def_id: LocalDefId,
    ) -> Result<fhir::VariantDef, ErrorGuaranteed> {
        let hir_id = self.tcx.hir().local_def_id_to_hir_id(def_id);
        let node = self.tcx.hir().get(hir_id);
        let hir::Node::Variant(variant) = node else { bug!("expected a variant") };
        self.lift_enum_variant(variant)
    }

    pub fn lift_enum_variant(
        &mut self,
        variant: &hir::Variant,
    ) -> Result<fhir::VariantDef, ErrorGuaranteed> {
        let item = self.tcx.hir().expect_item(self.owner.def_id);
        let hir::ItemKind::Enum(_, generics) = &item.kind else {
            bug!("expected an enum or struct")
        };

        let fields = variant
            .data
            .fields()
            .iter()
            .map(|field| self.lift_field_def(field))
            .try_collect_exhaust()?;

        let span = item.ident.span.to(generics.span);
        let path = fhir::Path {
            res: fhir::Res::SelfTyAlias { alias_to: self.owner.to_def_id(), is_trait_impl: false },
            args: vec![],
            bindings: vec![],
            refine: vec![],
            span,
        };
        let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
        let ret = fhir::VariantRet {
            bty,
            idx: fhir::RefineArg::Record(
                self.owner.to_def_id(),
                vec![],
                generics.span.shrink_to_hi(),
            ),
        };

        Ok(fhir::VariantDef {
            def_id: variant.def_id,
            params: vec![],
            fields,
            ret,
            span: variant.span,
            lifted: true,
        })
    }

    fn lift_ty(&mut self, ty: &hir::Ty) -> Result<fhir::Ty, ErrorGuaranteed> {
        let kind = match ty.kind {
            hir::TyKind::Slice(ty) => {
                let kind = fhir::BaseTyKind::Slice(Box::new(self.lift_ty(ty)?));
                let bty = fhir::BaseTy { kind, span: ty.span };
                return Ok(fhir::Ty {
                    kind: fhir::TyKind::BaseTy(bty),
                    fhir_id: self.next_fhir_id(),
                    span: ty.span,
                });
            }
            hir::TyKind::Array(ty, len) => {
                fhir::TyKind::Array(Box::new(self.lift_ty(ty)?), self.lift_array_len(len)?)
            }
            hir::TyKind::Ref(lft, mut_ty) => {
                fhir::TyKind::Ref(self.lift_lifetime(lft)?, self.lift_mut_ty(mut_ty)?)
            }
            hir::TyKind::Never => fhir::TyKind::Never,
            hir::TyKind::Tup(tys) => {
                fhir::TyKind::Tuple(tys.iter().map(|ty| self.lift_ty(ty)).try_collect()?)
            }
            hir::TyKind::Path(qpath) => return self.lift_qpath(qpath),
            hir::TyKind::Ptr(mut_ty) => {
                fhir::TyKind::RawPtr(Box::new(self.lift_ty(mut_ty.ty)?), mut_ty.mutbl)
            }
            hir::TyKind::OpaqueDef(item_id, args, in_trait_def) => {
                let opaque_ty = self
                    .with_new_owner(item_id.owner_id)
                    .lift_opaque_ty(item_id)?;
                self.insert_opaque_ty(item_id.owner_id.def_id, opaque_ty);

                let args = self.lift_generic_args(args)?;
                fhir::TyKind::OpaqueDef(item_id, args, vec![], in_trait_def)
            }
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::ty_to_string(ty)
                ));
            }
        };
        Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span: ty.span })
    }

    fn lift_lifetime(&self, lft: &hir::Lifetime) -> Result<fhir::Lifetime, ErrorGuaranteed> {
        self.tcx
            .named_bound_var(lft.hir_id)
            .map(fhir::Lifetime::Resolved)
            .ok_or_else(|| {
                let note = format!("cannot resolve lifetime: `{lft:?}`");
                self.sess
                    .emit_err(errors::UnsupportedHir::new(self.tcx, self.owner, &note))
            })
    }

    fn lift_mut_ty(&mut self, mut_ty: hir::MutTy) -> Result<fhir::MutTy, ErrorGuaranteed> {
        Ok(fhir::MutTy { ty: Box::new(self.lift_ty(mut_ty.ty)?), mutbl: mut_ty.mutbl })
    }

    fn lift_qpath(&mut self, qpath: hir::QPath) -> Result<fhir::Ty, ErrorGuaranteed> {
        match qpath {
            hir::QPath::Resolved(self_ty, path) => self.lift_path_to_ty(self_ty, path),
            hir::QPath::TypeRelative(_, _) | hir::QPath::LangItem(_, _, _) => {
                self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::qpath_to_string(&qpath)
                ))
            }
        }
    }

    fn lift_path(&mut self, path: &hir::Path) -> Result<fhir::Path, ErrorGuaranteed> {
        let Ok(res) = path.res.try_into() else {
            return self.emit_unsupported(&format!(
                "unsupported type: `{}` `{:?}`",
                rustc_hir_pretty::path_to_string(path),
                path.res
            ));
        };
        let (args, bindings) = match path.segments.last().unwrap().args {
            Some(args) => {
                (self.lift_generic_args(args.args)?, self.lift_type_bindings(args.bindings)?)
            }
            None => (vec![], vec![]),
        };

        Ok(fhir::Path { res, args, bindings, refine: vec![], span: path.span })
    }

    fn lift_path_to_ty(
        &mut self,
        self_ty: Option<&hir::Ty>,
        path: &hir::Path,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        let path = self.lift_path(path)?;
        let self_ty = self_ty
            .map(|ty| Ok(Box::new(self.lift_ty(ty)?)))
            .transpose()?;
        let qpath = fhir::QPath::Resolved(self_ty, path);
        let bty = fhir::BaseTy::from(qpath);
        let span = bty.span;
        Ok(fhir::Ty { kind: fhir::TyKind::BaseTy(bty), fhir_id: self.next_fhir_id(), span })
    }

    fn lift_generic_args(
        &mut self,
        args: &[hir::GenericArg<'_>],
    ) -> Result<Vec<fhir::GenericArg>, ErrorGuaranteed> {
        let mut lifted = vec![];
        for arg in args {
            match arg {
                hir::GenericArg::Lifetime(lft) => {
                    let lft = self.lift_lifetime(lft)?;
                    lifted.push(fhir::GenericArg::Lifetime(lft));
                }
                hir::GenericArg::Type(ty) => {
                    let ty = self.lift_ty(ty)?;
                    lifted.push(fhir::GenericArg::Type(ty));
                }
                hir::GenericArg::Const(_) => {
                    return self.emit_unsupported("const generics are not supported")
                }
                hir::GenericArg::Infer(_) => {
                    bug!("unexpected inference generic argument");
                }
            }
        }
        Ok(lifted)
    }

    fn lift_type_bindings(
        &mut self,
        bindings: &[hir::TypeBinding<'_>],
    ) -> Result<Vec<fhir::TypeBinding>, ErrorGuaranteed> {
        let mut lifted = vec![];
        for binding in bindings {
            let hir::TypeBindingKind::Equality { term } = binding.kind else {
                return self.emit_unsupported("unsupported type binding");
            };
            let hir::Term::Ty(term) = term else {
                return self.emit_unsupported("unsupported type binding");
            };
            let term = self.lift_ty(term)?;
            lifted.push(fhir::TypeBinding { ident: binding.ident, term });
        }
        Ok(lifted)
    }

    fn lift_array_len(&self, len: hir::ArrayLen) -> Result<fhir::ArrayLen, ErrorGuaranteed> {
        let body = match len {
            hir::ArrayLen::Body(anon_const) => self.tcx.hir().body(anon_const.body),
            hir::ArrayLen::Infer(_, _) => bug!("unexpected `ArrayLen::Infer`"),
        };
        if let hir::ExprKind::Lit(lit) = &body.value.kind
            && let LitKind::Int(array_len, _) = lit.node
        {
            Ok(fhir::ArrayLen { val: array_len as usize, span: lit.span })
        } else {
            self.emit_unsupported("only interger literals are supported for array lengths")
        }
    }

    /// HACK(nilehmann) do not use this function. See [`lift_self_ty`].
    fn generic_params_into_args(
        &self,
        generics: &hir::Generics,
    ) -> Result<Vec<fhir::GenericArg>, ErrorGuaranteed> {
        let mut args = vec![];
        for param in generics.params.iter() {
            match param.kind {
                hir::GenericParamKind::Type { .. } => {
                    let res = fhir::Res::Def(DefKind::TyParam, param.def_id.to_def_id());
                    let path = fhir::Path {
                        res,
                        args: vec![],
                        bindings: vec![],
                        refine: vec![],
                        span: param.span,
                    };
                    let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
                    let ty = fhir::Ty {
                        kind: fhir::TyKind::BaseTy(bty),
                        fhir_id: self.next_fhir_id(),
                        span: param.span,
                    };
                    args.push(fhir::GenericArg::Type(ty));
                }
                hir::GenericParamKind::Lifetime { .. } => {
                    let def_id = param.def_id.to_def_id();
                    let lft = fhir::Lifetime::Resolved(ResolvedArg::EarlyBound(def_id));
                    args.push(fhir::GenericArg::Lifetime(lft));
                }
                hir::GenericParamKind::Const { .. } => {
                    return self.emit_unsupported("const generics are not supported");
                }
            }
        }
        Ok(args)
    }

    fn insert_opaque_ty(&mut self, def_id: LocalDefId, opaque_ty: fhir::OpaqueTy) {
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item {def_id:?}"))
            .insert(def_id, opaque_ty);
    }

    #[track_caller]
    fn emit_unsupported<T>(&self, msg: &str) -> Result<T, ErrorGuaranteed> {
        self.emit_err(errors::UnsupportedHir::new(self.tcx, self.owner, msg))
    }

    #[track_caller]
    fn emit_err<'b, T>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<T, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }
}

pub mod errors {
    use flux_macros::Diagnostic;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_hir, code = "FLUX")]
    #[note]
    pub struct UnsupportedHir<'a> {
        #[primary_span]
        #[label]
        span: Span,
        def_kind: &'static str,
        note: &'a str,
    }

    impl<'a> UnsupportedHir<'a> {
        pub fn new(tcx: TyCtxt, def_id: impl Into<DefId>, note: &'a str) -> Self {
            let def_id = def_id.into();
            let span = tcx
                .def_ident_span(def_id)
                .unwrap_or_else(|| tcx.def_span(def_id));
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Self { span, def_kind, note }
        }
    }
}
