//! "Lift" HIR types into  FHIR types.

use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::ErrorGuaranteed;
use rustc_errors::Diagnostic;
use rustc_hir::{self as hir, def_id::LocalDefId, FnHeader, OwnerId};
use rustc_span::Span;

use super::{FhirId, FluxOwnerId};
use crate::{
    fhir::{self},
    global_env::GlobalEnv,
    try_alloc_slice, MaybeExternId,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub struct LiftCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    opaque_tys: Option<&'a mut Vec<&'genv fhir::OpaqueTy<'genv>>>,
    local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
    owner: MaybeExternId<OwnerId>,
}

impl<'a, 'genv, 'tcx> LiftCtxt<'a, 'genv, 'tcx> {
    pub fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        owner: MaybeExternId<OwnerId>,
        local_id_gen: &'a IndexGen<fhir::ItemLocalId>,
        opaque_tys: Option<&'a mut Vec<&'genv fhir::OpaqueTy<'genv>>>,
    ) -> Self {
        Self { genv, opaque_tys, local_id_gen, owner }
    }

    pub fn lift_generics(&mut self) -> Result<fhir::Generics<'genv>> {
        let generics = self.genv.hir().get_generics(self.local_id()).unwrap();
        self.lift_generics_inner(generics)
    }

    pub fn lift_refined_by<'fhir>(&self) -> fhir::RefinedBy<'fhir> {
        let item = self.genv.hir().expect_item(self.local_id());
        match item.kind {
            hir::ItemKind::TyAlias(..)
            | hir::ItemKind::Struct(..)
            | hir::ItemKind::Enum(..)
            | hir::ItemKind::Union(..) => fhir::RefinedBy::trivial(),
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
            hir::GenericParamKind::Type { default, .. } => {
                fhir::GenericParamKind::Type {
                    default: default.map(|ty| self.lift_ty(ty)).transpose()?,
                }
            }
            hir::GenericParamKind::Const { ty, .. } => {
                let ty = self.lift_ty(ty)?;
                fhir::GenericParamKind::Const { ty }
            }
        };
        Ok(fhir::GenericParam {
            def_id: self.genv.maybe_extern_id(param.def_id),
            name: param.name,
            kind,
        })
    }

    fn lift_generics_inner(&mut self, generics: &hir::Generics) -> Result<fhir::Generics<'genv>> {
        let params =
            try_alloc_slice!(self.genv, &generics.params, |param| self.lift_generic_param(param))?;
        let predicates = try_alloc_slice!(self.genv, &generics.predicates, |pred| {
            self.lift_where_predicate(pred)
        })?;

        Ok(fhir::Generics { params, refinement_params: &[], predicates })
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
            hir::GenericBound::Trait(poly_trait_ref) => {
                Ok(fhir::GenericBound::Trait(self.lift_poly_trait_ref(*poly_trait_ref)?))
            }
            hir::GenericBound::Outlives(lft) => {
                let lft = self.lift_lifetime(lft)?;
                Ok(fhir::GenericBound::Outlives(lft))
            }
            _ => self.emit_unsupported(&format!("unsupported generic bound: `{bound:?}`")),
        }
    }

    fn lift_poly_trait_ref(
        &mut self,
        poly_trait_ref: hir::PolyTraitRef,
    ) -> Result<fhir::PolyTraitRef<'genv>> {
        let modifiers = match poly_trait_ref.modifiers {
            rustc_hir::TraitBoundModifiers {
                constness: rustc_hir::BoundConstness::Never,
                polarity: rustc_hir::BoundPolarity::Positive,
            } => fhir::TraitBoundModifier::None,
            rustc_hir::TraitBoundModifiers {
                constness: rustc_hir::BoundConstness::Never,
                polarity: rustc_hir::BoundPolarity::Maybe(_),
            } => fhir::TraitBoundModifier::Maybe,
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported trait modifiers: `{:?}`",
                    poly_trait_ref.modifiers,
                ));
            }
        };
        let bound_generic_params =
            try_alloc_slice!(self.genv, &poly_trait_ref.bound_generic_params, |param| {
                self.lift_generic_param(param)
            })?;
        let trait_ref = self.lift_path(poly_trait_ref.trait_ref.path)?;
        Ok(fhir::PolyTraitRef {
            bound_generic_params,
            modifiers,
            trait_ref,
            span: poly_trait_ref.span,
        })
    }

    fn lift_opaque_ty(&mut self, opaque_ty: &hir::OpaqueTy) -> Result<fhir::OpaqueTy<'genv>> {
        let bounds =
            try_alloc_slice!(self.genv, &opaque_ty.bounds, |bound| self.lift_generic_bound(bound))?;

        Ok(fhir::OpaqueTy { def_id: MaybeExternId::Local(opaque_ty.def_id), bounds })
    }

    pub fn lift_fn_header(&mut self) -> FnHeader {
        let hir_id = self.genv.tcx().local_def_id_to_hir_id(self.local_id());
        self.genv
            .hir()
            .fn_sig_by_hir_id(hir_id)
            .expect("item does not have a `FnDecl`")
            .header
    }

    pub fn lift_fn_decl(&mut self) -> Result<fhir::FnDecl<'genv>> {
        let hir_id = self.genv.tcx().local_def_id_to_hir_id(self.local_id());
        let fn_sig = self
            .genv
            .hir()
            .fn_sig_by_hir_id(hir_id)
            .expect("item does not have a `FnDecl`");

        self.lift_fn_decl_inner(fn_sig.span, fn_sig.decl)
    }

    fn lift_fn_decl_inner(
        &mut self,
        span: Span,
        decl: &hir::FnDecl,
    ) -> Result<fhir::FnDecl<'genv>> {
        let inputs = try_alloc_slice!(self.genv, &decl.inputs, |ty| self.lift_ty(ty))?;

        let output =
            fhir::FnOutput { params: &[], ensures: &[], ret: self.lift_fn_ret_ty(&decl.output)? };

        Ok(fhir::FnDecl { requires: &[], inputs, output, span, lifted: true })
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

    pub fn lift_type_alias(&mut self) -> Result<fhir::Item<'genv>> {
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::TyAlias(ty, _) = item.kind else {
            bug!("expected type alias");
        };

        let generics = self.lift_generics()?;
        let ty = self.lift_ty(ty)?;
        let ty_alias = fhir::TyAlias { index: None, ty, span: item.span, lifted: true };
        Ok(fhir::Item { generics, kind: fhir::ItemKind::TyAlias(ty_alias), owner_id: self.owner })
    }

    pub fn lift_field_def_id(&mut self, def_id: LocalDefId) -> Result<fhir::FieldDef<'genv>> {
        let hir::Node::Field(field_def) = self.genv.tcx().hir_node_by_def_id(def_id) else {
            bug!("expected a field")
        };
        self.lift_field_def(field_def)
    }

    pub fn lift_field_def(&mut self, field_def: &hir::FieldDef) -> Result<fhir::FieldDef<'genv>> {
        let ty = self.lift_ty(field_def.ty)?;
        Ok(fhir::FieldDef { ty, lifted: true })
    }

    pub fn lift_enum_variant_id(&mut self, def_id: LocalDefId) -> Result<fhir::VariantDef<'genv>> {
        let node = self.genv.tcx().hir_node_by_def_id(def_id);
        let hir::Node::Variant(variant) = node else { bug!("expected a variant") };
        self.lift_enum_variant(variant)
    }

    pub fn lift_enum_variant(&mut self, variant: &hir::Variant) -> Result<fhir::VariantDef<'genv>> {
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };

        let fields = try_alloc_slice!(self.genv, variant.data.fields(), |field| {
            self.lift_field_def(field)
        })?;

        let ret = self.lift_variant_ret_inner(generics);

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
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };
        self.lift_variant_ret_inner(generics)
    }

    fn lift_variant_ret_inner(&mut self, generics: &hir::Generics) -> fhir::VariantRet<'genv> {
        let kind = fhir::ExprKind::Record(&[]);
        fhir::VariantRet {
            enum_id: self.owner.resolved_id(),
            idx: fhir::Expr {
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
                let bty = fhir::BaseTy { kind, fhir_id: self.next_fhir_id(), span: ty.span };
                return Ok(fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: ty.span });
            }
            hir::TyKind::Array(ty, len) => {
                let ty = self.lift_ty(ty)?;
                fhir::TyKind::Array(self.genv.alloc(ty), self.lift_array_len(len)?)
            }
            hir::TyKind::Ref(lft, mut_ty) => {
                fhir::TyKind::Ref(self.lift_lifetime(lft)?, self.lift_mut_ty(mut_ty)?)
            }
            hir::TyKind::BareFn(bare_fn) => {
                let bare_fn = self.lift_bare_fn(ty.span, bare_fn)?;
                fhir::TyKind::BareFn(self.genv.alloc(bare_fn))
            }
            hir::TyKind::Never => fhir::TyKind::Never,
            hir::TyKind::Tup(tys) => {
                let tys = try_alloc_slice!(self.genv, tys, |ty| self.lift_ty(ty))?;
                fhir::TyKind::Tuple(tys)
            }
            hir::TyKind::Path(qpath) => {
                let qpath = self.lift_qpath(qpath)?;
                let bty = fhir::BaseTy::from_qpath(qpath, self.next_fhir_id());
                return Ok(fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: bty.span });
            }
            hir::TyKind::Ptr(mut_ty) => {
                let ty = self.lift_ty(mut_ty.ty)?;
                fhir::TyKind::RawPtr(self.genv.alloc(ty), mut_ty.mutbl)
            }
            hir::TyKind::OpaqueDef(opaque_ty) => {
                let opaque_ty = self.lift_opaque_ty(opaque_ty)?;
                let opaque_ty = self.insert_opaque_ty(opaque_ty);
                fhir::TyKind::OpaqueDef(opaque_ty)
            }
            hir::TyKind::TraitObject(poly_traits, lft, syntax) => {
                let poly_traits = try_alloc_slice!(self.genv, poly_traits, |poly_trait| {
                    if poly_trait.modifiers != hir::TraitBoundModifiers::NONE {
                        return self.emit_unsupported(&format!(
                            "unsupported type: `{}`",
                            rustc_hir_pretty::ty_to_string(&self.genv.tcx(), ty)
                        ));
                    }
                    self.lift_poly_trait_ref(*poly_trait)
                })?;

                let lft = self.lift_lifetime(lft)?;
                fhir::TyKind::TraitObject(poly_traits, lft, syntax)
            }
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::ty_to_string(&self.genv.tcx(), ty)
                ));
            }
        };
        Ok(fhir::Ty { kind, span: ty.span })
    }

    fn lift_bare_fn(
        &mut self,
        span: Span,
        bare_fn: &hir::BareFnTy,
    ) -> Result<fhir::BareFnTy<'genv>> {
        let generic_params = try_alloc_slice!(self.genv, bare_fn.generic_params, |param| {
            self.lift_generic_param(param)
        })?;
        let decl = self.lift_fn_decl_inner(span, bare_fn.decl)?;
        Ok(fhir::BareFnTy {
            safety: bare_fn.safety,
            abi: bare_fn.abi,
            generic_params,
            decl: self.genv.alloc(decl),
            param_names: self.genv.alloc_slice(bare_fn.param_names),
        })
    }

    fn lift_lifetime(&self, lft: &hir::Lifetime) -> Result<fhir::Lifetime> {
        self.genv
            .tcx()
            .named_bound_var(lft.hir_id)
            .map(fhir::Lifetime::Resolved)
            .ok_or_else(|| {
                let note = format!("cannot resolve lifetime: `{lft:?}`");
                self.emit_unsupported::<!>(&note).into_err()
            })
    }

    fn lift_mut_ty(&mut self, mut_ty: hir::MutTy) -> Result<fhir::MutTy<'genv>> {
        let ty = self.lift_ty(mut_ty.ty)?;
        Ok(fhir::MutTy { ty: self.genv.alloc(ty), mutbl: mut_ty.mutbl })
    }

    fn lift_qpath(&mut self, qpath: hir::QPath) -> Result<fhir::QPath<'genv>> {
        match qpath {
            hir::QPath::Resolved(qself, path) => {
                let qself = qself
                    .map(|ty| {
                        let ty = self.lift_ty(ty)?;
                        Ok(self.genv.alloc(ty))
                    })
                    .transpose()?;
                let path = self.lift_path(path)?;
                Ok(fhir::QPath::Resolved(qself, path))
            }
            hir::QPath::TypeRelative(qself, segment) => {
                let qself = self.lift_ty(qself)?;
                let segment = self.lift_path_segment(segment)?;
                Ok(fhir::QPath::TypeRelative(self.genv.alloc(qself), self.genv.alloc(segment)))
            }
            hir::QPath::LangItem(_, _) => {
                self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::qpath_to_string(&self.genv.tcx(), &qpath)
                ))
            }
        }
    }

    fn lift_path(&mut self, path: &hir::Path) -> Result<fhir::Path<'genv>> {
        let Ok(res) = path.res.try_into() else {
            return self.emit_unsupported(&format!("unsupported res: `{:?}`", path.res));
        };
        let segments =
            try_alloc_slice!(self.genv, path.segments, |segment| self.lift_path_segment(segment))?;

        Ok(fhir::Path { res, fhir_id: self.next_fhir_id(), segments, refine: &[], span: path.span })
    }

    fn lift_path_segment(
        &mut self,
        segment: &hir::PathSegment,
    ) -> Result<fhir::PathSegment<'genv>> {
        let Ok(res) = segment.res.try_into() else {
            return self.emit_unsupported(&format!("unsupported res: `{:?}`", segment.res));
        };
        let (args, bindings) = {
            match segment.args {
                Some(args) => {
                    (
                        self.lift_generic_args(args.args)?,
                        self.lift_assoc_item_constraints(args.constraints)?,
                    )
                }
                None => ([].as_slice(), [].as_slice()),
            }
        };

        Ok(fhir::PathSegment { res, ident: segment.ident, args, constraints: bindings })
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
                hir::GenericArg::Const(const_arg) => {
                    Ok(fhir::GenericArg::Const(self.lift_const_arg(const_arg)))
                }
                hir::GenericArg::Infer(_) => {
                    bug!("unexpected inference generic argument");
                }
            }
        })
    }

    fn lift_assoc_item_constraints(
        &mut self,
        constraints: &[hir::AssocItemConstraint<'_>],
    ) -> Result<&'genv [fhir::AssocItemConstraint<'genv>]> {
        try_alloc_slice!(self.genv, constraints, |cstr| {
            let hir::AssocItemConstraintKind::Equality { term } = cstr.kind else {
                return self.emit_unsupported("unsupported type binding");
            };
            let hir::Term::Ty(term) = term else {
                return self.emit_unsupported("unsupported type binding");
            };
            let kind = fhir::AssocItemConstraintKind::Equality { term: self.lift_ty(term)? };
            Ok(fhir::AssocItemConstraint { ident: cstr.ident, kind })
        })
    }

    fn lift_array_len(&mut self, len: hir::ArrayLen) -> Result<fhir::ConstArg> {
        match len {
            hir::ArrayLen::Body(const_arg) => Ok(self.lift_const_arg(const_arg)),
            hir::ArrayLen::Infer(_) => bug!("unexpected `ArrayLen::Infer`"),
        }
    }

    fn lift_const_arg(&mut self, const_arg: &hir::ConstArg) -> fhir::ConstArg {
        fhir::ConstArg { kind: fhir::ConstArgKind::Infer, span: const_arg.span() }
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

    #[track_caller]
    fn emit_unsupported<T>(&self, note: &str) -> Result<T> {
        let tcx = self.genv.tcx();
        let local_id = self.owner.local_id().def_id;
        let span = tcx
            .def_ident_span(local_id)
            .unwrap_or_else(|| tcx.def_span(local_id));
        let def_kind = tcx.def_descr(local_id.to_def_id());
        self.emit_err(errors::UnsupportedHir { span, def_kind, note })
    }

    #[track_caller]
    fn emit_err<'b, T>(&'b self, err: impl Diagnostic<'b>) -> Result<T> {
        Err(self.genv.sess().emit_err(err))
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId {
            owner: FluxOwnerId::Rust(self.owner.local_id()),
            local_id: self.local_id_gen.fresh(),
        }
    }

    fn local_id(&self) -> LocalDefId {
        self.owner.local_id().def_id
    }
}

pub mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(middle_unsupported_hir, code = E0999)]
    #[note]
    pub(super) struct UnsupportedHir<'a> {
        #[primary_span]
        #[label]
        pub span: Span,
        pub def_kind: &'static str,
        pub note: &'a str,
    }
}
