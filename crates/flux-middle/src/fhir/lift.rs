//! "Lift" HIR types into  FHIR types.
//!
use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::ErrorGuaranteed;
use hir::{def::DefKind, OwnerId};
use rustc_ast::LitKind;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::middle::resolve_bound_vars::ResolvedArg;

use super::{FhirId, FluxOwnerId};
use crate::{fhir, global_env::GlobalEnv, try_alloc_slice};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub struct LiftCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
}

pub fn lift_type_alias<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
) -> Result<fhir::TyAlias<'genv>> {
    let def_id = owner_id.def_id;
    let item = genv.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(ty, _) = item.kind else {
        bug!("expected type alias");
    };
    let local_id_gen = IndexGen::new();
    let mut cx = LiftCtxt::new(genv, owner_id, &local_id_gen, None);

    let generics = cx.lift_generics()?;
    let refined_by = cx.lift_refined_by();
    let ty = cx.lift_ty(ty)?;
    Ok(fhir::TyAlias {
        owner_id,
        generics,
        refined_by: genv.alloc(refined_by),
        index_params: &[],
        ty,
        span: item.span,
        lifted: true,
    })
}

pub fn lift_fn<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
) -> Result<(fhir::FnSig<'genv>, UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>)> {
    let mut opaque_tys = Default::default();
    let local_id_gen = IndexGen::new();
    let mut cx = LiftCtxt::new(genv, owner_id, &local_id_gen, Some(&mut opaque_tys));
    let fn_sig = cx.lift_fn_sig()?;
    Ok((fn_sig, opaque_tys))
}

/// HACK(nilehmann) this is used during annot check to allow an explicit type to refine [`Self`].
/// For example, in `impl List<T> { fn foo(&self) }` the type of `self` is `&Self` and we want to
/// allow a refinement using `&List<T>`.
/// Do not use this outside of annot check because the `FhirId`s will be wrong.
///
/// [`Self`]: fhir::Res::SelfTyAlias
pub fn lift_self_ty<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner_id: OwnerId,
) -> Result<Option<fhir::Ty<'genv>>> {
    if let Some(def_id) = genv.tcx().impl_of_method(owner_id.to_def_id()) {
        let owner_id = OwnerId { def_id: def_id.expect_local() };
        let local_id_gen = IndexGen::new();
        let mut cx = LiftCtxt::new(genv, owner_id, &local_id_gen, None);
        let local_id = def_id.expect_local();
        let hir::Item { kind: hir::ItemKind::Impl(impl_), .. } = genv.hir().expect_item(local_id)
        else {
            bug!("expected an impl")
        };
        let self_ty = cx.lift_ty(impl_.self_ty)?;
        Ok(Some(self_ty))
    } else if let def_kind @ (DefKind::Struct | DefKind::Enum) = genv.def_kind(owner_id) {
        let generics = genv.hir().get_generics(owner_id.def_id).unwrap();
        let item = genv.hir().expect_item(owner_id.def_id);

        let local_id_gen = IndexGen::new();
        let cx = LiftCtxt::new(genv, owner_id, &local_id_gen, None);

        let span = item.ident.span.to(generics.span);
        let path = fhir::Path {
            res: fhir::Res::Def(def_kind, owner_id.to_def_id()),
            args: cx.generic_params_into_args(generics)?,
            bindings: &[],
            refine: &[],
            span,
        };
        let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
        Ok(Some(fhir::Ty { span, kind: fhir::TyKind::BaseTy(bty) }))
    } else {
        Ok(None)
    }
}

impl<'a, 'genv, 'tcx> LiftCtxt<'a, 'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        owner: OwnerId,
        local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    ) -> Self {
        Self { genv, opaque_tys, local_id_gen, owner }
    }

    fn with_new_owner<'b>(
        &'b mut self,
        owner: OwnerId,
        local_id_gen: &'b IndexGen<fhir::ItemLocalId>,
    ) -> LiftCtxt<'b, 'genv, 'tcx> {
        LiftCtxt::new(self.genv, owner, local_id_gen, self.opaque_tys.as_deref_mut())
    }

    pub fn lift_generics(&mut self) -> Result<fhir::Generics<'genv>> {
        let generics = self.genv.hir().get_generics(self.owner.def_id).unwrap();
        self.lift_generics_inner(generics)
    }

    pub fn lift_refined_by<'fhir>(&self) -> fhir::RefinedBy<'fhir> {
        let def_id = self.owner.def_id;
        let item = self.genv.hir().expect_item(def_id);
        match item.kind {
            hir::ItemKind::TyAlias(..) | hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) => {
                fhir::RefinedBy::trivial(item.ident.span)
            }
            _ => {
                bug!("expected struct, enum, or type alias");
            }
        }
    }

    pub fn lift_generic_param(
        &mut self,
        param: &hir::GenericParam,
    ) -> Result<fhir::GenericParam<'genv>> {
        let kind = match param.kind {
            hir::GenericParamKind::Lifetime { .. } => fhir::GenericParamKind::Lifetime,
            hir::GenericParamKind::Type { default, synthetic: false } => {
                fhir::GenericParamKind::Type {
                    default: default.map(|ty| self.lift_ty(ty)).transpose()?,
                }
            }
            hir::GenericParamKind::Type { synthetic: true, .. } => {
                return self.emit_err(errors::UnsupportedHir::new(
                    self.genv.tcx(),
                    param.def_id,
                    "`impl Trait` in argument position not supported",
                ))
            }
            hir::GenericParamKind::Const { .. } => {
                return self.emit_err(errors::UnsupportedHir::new(
                    self.genv.tcx(),
                    param.def_id,
                    "const generics are not supported",
                ))
            }
        };
        Ok(fhir::GenericParam { def_id: param.def_id, kind })
    }

    fn lift_generics_inner(&mut self, generics: &hir::Generics) -> Result<fhir::Generics<'genv>> {
        let params =
            try_alloc_slice!(self.genv, &generics.params, |param| self.lift_generic_param(param))?;
        let predicates = try_alloc_slice!(self.genv, &generics.predicates, |pred| {
            self.lift_where_predicate(pred)
        })?;

        Ok(fhir::Generics { params, self_kind: None, refinement_params: &[], predicates })
    }

    fn lift_where_predicate(
        &mut self,
        pred: &hir::WherePredicate,
    ) -> Result<fhir::WhereBoundPredicate<'genv>> {
        if let hir::WherePredicate::BoundPredicate(bound) = pred {
            if !bound.bound_generic_params.is_empty() {
                return self.emit_unsupported("higher-rank trait bounds are not supported");
            }
            let bounded_ty = self.lift_ty(bound.bounded_ty)?;
            let bounds =
                try_alloc_slice!(self.genv, &bound.bounds, |bound| self.lift_generic_bound(bound))?;

            Ok(fhir::WhereBoundPredicate { bounded_ty, bounds, span: bound.span })
        } else {
            self.emit_unsupported(&format!("unsupported where predicate: `{pred:?}`"))
        }
    }

    fn lift_generic_bound(
        &mut self,
        bound: &hir::GenericBound,
    ) -> Result<fhir::GenericBound<'genv>> {
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
    ) -> Result<fhir::PolyTraitRef<'genv>> {
        let bound_generic_params =
            try_alloc_slice!(self.genv, &poly_trait_ref.bound_generic_params, |param| {
                self.lift_generic_param(param)
            })?;
        Ok(fhir::PolyTraitRef {
            bound_generic_params,
            trait_ref: self.lift_path(poly_trait_ref.trait_ref.path)?,
        })
    }

    fn lift_opaque_ty(&mut self) -> Result<fhir::OpaqueTy<'genv>> {
        let hir::ItemKind::OpaqueTy(opaque_ty) =
            self.genv.hir().expect_item(self.owner.def_id).kind
        else {
            bug!("expected opaque type")
        };

        let bounds =
            try_alloc_slice!(self.genv, &opaque_ty.bounds, |bound| self.lift_generic_bound(bound))?;

        let opaque_ty =
            fhir::OpaqueTy { generics: self.lift_generics_inner(opaque_ty.generics)?, bounds };
        Ok(opaque_ty)
    }

    pub fn lift_fn_sig(&mut self) -> Result<fhir::FnSig<'genv>> {
        let hir_id = self.genv.hir().local_def_id_to_hir_id(self.owner.def_id);
        let fn_sig = self
            .genv
            .hir()
            .fn_sig_by_hir_id(hir_id)
            .expect("item does not have a `FnDecl`");

        let generics = self.lift_generics()?;
        let args = try_alloc_slice!(self.genv, &fn_sig.decl.inputs, |ty| self.lift_ty(ty))?;

        let output = fhir::FnOutput {
            params: &[],
            ensures: &[],
            ret: self.lift_fn_ret_ty(&fn_sig.decl.output)?,
        };

        let fn_sig =
            fhir::FnSig { generics, requires: &[], args, output, lifted: true, span: fn_sig.span };
        Ok(fn_sig)
    }

    fn lift_fn_ret_ty(&mut self, ret_ty: &hir::FnRetTy) -> Result<fhir::Ty<'genv>> {
        match ret_ty {
            hir::FnRetTy::DefaultReturn(_) => {
                let kind = fhir::TyKind::Tuple(&[]);
                Ok(fhir::Ty { kind, span: ret_ty.span() })
            }
            hir::FnRetTy::Return(ty) => self.lift_ty(ty),
        }
    }

    pub fn lift_type_alias(&mut self) -> Result<fhir::TyAlias<'genv>> {
        let item = self.genv.hir().expect_item(self.owner.def_id);
        let hir::ItemKind::TyAlias(ty, _) = item.kind else {
            bug!("expected type alias");
        };

        let generics = self.lift_generics()?;
        let refined_by = self.lift_refined_by();
        let ty = self.lift_ty(ty)?;
        Ok(fhir::TyAlias {
            owner_id: self.owner,
            generics,
            refined_by: self.genv.alloc(refined_by),
            index_params: &[],
            ty,
            span: item.span,
            lifted: true,
        })
    }

    pub fn lift_field_def_id(&mut self, def_id: LocalDefId) -> Result<fhir::FieldDef<'genv>> {
        let hir = self.genv.hir();
        let hir_id = hir.local_def_id_to_hir_id(def_id);
        let hir::Node::Field(field_def) = hir.get(hir_id) else { bug!("expected a field") };
        Ok(fhir::FieldDef { def_id, ty: self.lift_ty(field_def.ty)?, lifted: true })
    }

    pub fn lift_field_def(&mut self, field_def: &hir::FieldDef) -> Result<fhir::FieldDef<'genv>> {
        let ty = self.lift_ty(field_def.ty)?;
        Ok(fhir::FieldDef { def_id: field_def.def_id, ty, lifted: true })
    }

    pub fn lift_enum_variant_id(&mut self, def_id: LocalDefId) -> Result<fhir::VariantDef<'genv>> {
        let hir_id = self.genv.hir().local_def_id_to_hir_id(def_id);
        let node = self.genv.hir().get(hir_id);
        let hir::Node::Variant(variant) = node else { bug!("expected a variant") };
        self.lift_enum_variant(variant)
    }

    pub fn lift_enum_variant(&mut self, variant: &hir::Variant) -> Result<fhir::VariantDef<'genv>> {
        let item = self.genv.hir().expect_item(self.owner.def_id);
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };

        let fields = try_alloc_slice!(self.genv, variant.data.fields(), |field| {
            self.lift_field_def(field)
        })?;

        let ret = self.lift_variant_ret_inner(item, generics);

        Ok(fhir::VariantDef {
            def_id: variant.def_id,
            params: &[],
            fields,
            ret,
            span: variant.span,
            lifted: true,
        })
    }

    pub fn lift_variant_ret(&mut self) -> fhir::VariantRet<'genv> {
        let item = self.genv.hir().expect_item(self.owner.def_id);
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };
        self.lift_variant_ret_inner(item, generics)
    }

    fn lift_variant_ret_inner(
        &mut self,
        item: &hir::Item,
        generics: &hir::Generics,
    ) -> fhir::VariantRet<'genv> {
        let span = item.ident.span.to(generics.span);
        let path = fhir::Path {
            res: fhir::Res::SelfTyAlias { alias_to: self.owner.to_def_id(), is_trait_impl: false },
            args: &[],
            bindings: &[],
            refine: &[],
            span,
        };
        let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
        let kind = fhir::RefineArgKind::Record(&[]);
        fhir::VariantRet {
            bty,
            idx: fhir::RefineArg {
                kind,
                fhir_id: self.next_fhir_id(),
                span: generics.span.shrink_to_hi(),
            },
        }
    }

    pub fn lift_ty(&mut self, ty: &hir::Ty) -> Result<fhir::Ty<'genv>> {
        let kind = match ty.kind {
            hir::TyKind::Slice(ty) => {
                let ty = self.lift_ty(ty)?;
                let kind = fhir::BaseTyKind::Slice(self.genv.alloc(ty));
                let bty = fhir::BaseTy { kind, span: ty.span };
                return Ok(fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: ty.span });
            }
            hir::TyKind::Array(ty, len) => {
                let ty = self.lift_ty(ty)?;
                fhir::TyKind::Array(self.genv.alloc(ty), self.lift_array_len(len)?)
            }
            hir::TyKind::Ref(lft, mut_ty) => {
                fhir::TyKind::Ref(self.lift_lifetime(lft)?, self.lift_mut_ty(mut_ty)?)
            }
            hir::TyKind::Never => fhir::TyKind::Never,
            hir::TyKind::Tup(tys) => {
                let tys = try_alloc_slice!(self.genv, tys, |ty| self.lift_ty(ty))?;
                fhir::TyKind::Tuple(tys)
            }
            hir::TyKind::Path(qpath) => return self.lift_qpath(qpath),
            hir::TyKind::Ptr(mut_ty) => {
                let ty = self.lift_ty(mut_ty.ty)?;
                fhir::TyKind::RawPtr(self.genv.alloc(ty), mut_ty.mutbl)
            }
            hir::TyKind::OpaqueDef(item_id, args, in_trait_def) => {
                let opaque_ty = self
                    .with_new_owner(item_id.owner_id, &IndexGen::new())
                    .lift_opaque_ty()?;
                self.insert_opaque_ty(item_id.owner_id.def_id, opaque_ty);

                let args = self.lift_generic_args(args)?;
                fhir::TyKind::OpaqueDef(item_id, args, &[], in_trait_def)
            }
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::ty_to_string(ty)
                ));
            }
        };
        Ok(fhir::Ty { kind, span: ty.span })
    }

    fn lift_lifetime(&self, lft: &hir::Lifetime) -> Result<fhir::Lifetime> {
        self.genv
            .tcx()
            .named_bound_var(lft.hir_id)
            .map(fhir::Lifetime::Resolved)
            .ok_or_else(|| {
                let note = format!("cannot resolve lifetime: `{lft:?}`");
                self.genv.sess().emit_err(errors::UnsupportedHir::new(
                    self.genv.tcx(),
                    self.owner,
                    &note,
                ))
            })
    }

    fn lift_mut_ty(&mut self, mut_ty: hir::MutTy) -> Result<fhir::MutTy<'genv>> {
        let ty = self.lift_ty(mut_ty.ty)?;
        Ok(fhir::MutTy { ty: self.genv.alloc(ty), mutbl: mut_ty.mutbl })
    }

    fn lift_qpath(&mut self, qpath: hir::QPath) -> Result<fhir::Ty<'genv>> {
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

    fn lift_path(&mut self, path: &hir::Path) -> Result<fhir::Path<'genv>> {
        let Ok(res) = path.res.try_into() else {
            return self.emit_unsupported(&format!("unsupported res: `{:?}`", path.res));
        };
        let (args, bindings) = match path.segments.last().unwrap().args {
            Some(args) => {
                (self.lift_generic_args(args.args)?, self.lift_type_bindings(args.bindings)?)
            }
            None => ([].as_slice(), [].as_slice()),
        };

        Ok(fhir::Path { res, args, bindings, refine: &[], span: path.span })
    }

    fn lift_path_to_ty(
        &mut self,
        self_ty: Option<&hir::Ty>,
        path: &hir::Path,
    ) -> Result<fhir::Ty<'genv>> {
        let path = self.lift_path(path)?;
        let self_ty = self_ty
            .map(|ty| {
                let ty = self.lift_ty(ty)?;
                Ok(self.genv.alloc(ty))
            })
            .transpose()?;
        let qpath = fhir::QPath::Resolved(self_ty, path);
        let bty = fhir::BaseTy::from(qpath);
        let span = bty.span;
        Ok(fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span })
    }

    fn lift_generic_args(
        &mut self,
        args: &[hir::GenericArg<'_>],
    ) -> Result<&'genv [fhir::GenericArg<'genv>]> {
        try_alloc_slice!(self.genv, args, |arg| {
            match arg {
                hir::GenericArg::Lifetime(lft) => {
                    let lft = self.lift_lifetime(lft)?;
                    Ok(fhir::GenericArg::Lifetime(lft))
                }
                hir::GenericArg::Type(ty) => {
                    let ty = self.lift_ty(ty)?;
                    Ok(fhir::GenericArg::Type(self.genv.alloc(ty)))
                }
                hir::GenericArg::Const(_) => {
                    self.emit_unsupported("const generics are not supported")
                }
                hir::GenericArg::Infer(_) => {
                    bug!("unexpected inference generic argument");
                }
            }
        })
    }

    fn lift_type_bindings(
        &mut self,
        bindings: &[hir::TypeBinding<'_>],
    ) -> Result<&'genv [fhir::TypeBinding<'genv>]> {
        try_alloc_slice!(self.genv, bindings, |binding| {
            let hir::TypeBindingKind::Equality { term } = binding.kind else {
                return self.emit_unsupported("unsupported type binding");
            };
            let hir::Term::Ty(term) = term else {
                return self.emit_unsupported("unsupported type binding");
            };
            let term = self.lift_ty(term)?;
            Ok(fhir::TypeBinding { ident: binding.ident, term })
        })
    }

    fn lift_array_len(&self, len: hir::ArrayLen) -> Result<fhir::ArrayLen> {
        let body = match len {
            hir::ArrayLen::Body(anon_const) => self.genv.hir().body(anon_const.body),
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
    ) -> Result<&'genv [fhir::GenericArg<'genv>]> {
        try_alloc_slice!(self.genv, generics.params, |param| {
            match param.kind {
                hir::GenericParamKind::Type { .. } => {
                    let res = fhir::Res::Def(DefKind::TyParam, param.def_id.to_def_id());
                    let path =
                        fhir::Path { res, args: &[], bindings: &[], refine: &[], span: param.span };
                    let bty = fhir::BaseTy::from(fhir::QPath::Resolved(None, path));
                    let ty = fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: param.span };
                    Ok(fhir::GenericArg::Type(self.genv.alloc(ty)))
                }
                hir::GenericParamKind::Lifetime { .. } => {
                    let def_id = param.def_id.to_def_id();
                    let lft = fhir::Lifetime::Resolved(ResolvedArg::EarlyBound(def_id));
                    Ok(fhir::GenericArg::Lifetime(lft))
                }
                hir::GenericParamKind::Const { .. } => {
                    self.emit_unsupported("const generics are not supported")
                }
            }
        })
    }

    fn insert_opaque_ty(&mut self, def_id: LocalDefId, opaque_ty: fhir::OpaqueTy<'genv>) {
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item {def_id:?}"))
            .insert(def_id, opaque_ty);
    }

    #[track_caller]
    fn emit_unsupported<T>(&self, msg: &str) -> Result<T> {
        self.emit_err(errors::UnsupportedHir::new(self.genv.tcx(), self.owner, msg))
    }

    #[track_caller]
    fn emit_err<'b, T>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<T> {
        Err(self.genv.sess().emit_err(err))
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
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
