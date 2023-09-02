//! "Lift" HIR types into  FHIR types.
//!
use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use hir::{def::DefKind, OwnerId};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use super::{FhirId, FluxOwnerId};
use crate::fhir;

struct LiftCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: OwnerId,
}

pub fn lift_generics(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<fhir::Generics, ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    let hir_generics = tcx.hir().get_generics(def_id).unwrap();
    let cx = LiftCtxt::new(tcx, sess, owner_id);

    let params = hir_generics
        .params
        .iter()
        .map(|param| {
            let kind = match param.kind {
                hir::GenericParamKind::Lifetime { .. } => fhir::GenericParamDefKind::Lifetime,
                hir::GenericParamKind::Type { default, synthetic: false } => {
                    fhir::GenericParamDefKind::Type {
                        default: default.map(|ty| cx.lift_ty(ty)).transpose()?,
                    }
                }
                hir::GenericParamKind::Type { synthetic: true, .. } => {
                    return Err(sess.emit_err(errors::UnsupportedHir::new(
                        tcx,
                        param.def_id,
                        "`impl Trait` in argument position not supported",
                    )))
                }
                hir::GenericParamKind::Const { .. } => {
                    return Err(sess.emit_err(errors::UnsupportedHir::new(
                        tcx,
                        param.def_id,
                        "const generics are not supported",
                    )))
                }
            };
            Ok(fhir::GenericParamDef { def_id: param.def_id, kind })
        })
        .try_collect_exhaust()?;
    Ok(fhir::Generics { params })
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
) -> Result<fhir::TyAlias, ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    let item = tcx.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(ty, _) = &item.kind else {
        bug!("expected type alias");
    };
    let cx = LiftCtxt::new(tcx, sess, owner_id);
    let ty = cx.lift_ty(ty)?;
    Ok(fhir::TyAlias {
        owner_id,
        early_bound_params: vec![],
        index_params: vec![],
        ty,
        span: item.span,
        lifted: true,
    })
}

pub fn lift_field_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
) -> Result<fhir::FieldDef, ErrorGuaranteed> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let node = tcx.hir().get(hir_id);
    let hir::Node::Field(field_def) = node else { bug!("expected a field") };
    let struct_id = tcx.hir().get_parent_item(hir_id);
    let ty = LiftCtxt::new(tcx, sess, struct_id).lift_ty(field_def.ty)?;
    Ok(fhir::FieldDef { def_id, ty, lifted: true })
}

pub fn lift_enum_variant_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
) -> Result<fhir::VariantDef, ErrorGuaranteed> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let node = tcx.hir().get(hir_id);
    let hir::Node::Variant(variant) = node else { bug!("expected a variant") };
    let enum_id = tcx.hir().get_parent_item(hir_id);
    let hir::Item { ident, kind: hir::ItemKind::Enum(..), .. } =
        tcx.hir().expect_item(enum_id.def_id)
    else {
        bug!("expected an enum")
    };

    let cx = LiftCtxt::new(tcx, sess, enum_id);

    let fields = variant
        .data
        .fields()
        .iter()
        .map(|field| cx.lift_field_def(field))
        .try_collect_exhaust()?;

    // FIXME(nilehmann) the span should also include the generic arguments
    let span = ident.span;
    let path = fhir::Path {
        res: fhir::Res::SelfTyAlias { alias_to: enum_id.to_def_id(), is_trait_impl: false },
        args: vec![],
        bindings: vec![],
        refine: vec![],
        span,
    };
    let ret = fhir::VariantRet {
        bty: fhir::BaseTy::from(fhir::QPath::Resolved(None, path)),
        idx: fhir::RefineArg::Record(enum_id.to_def_id(), vec![], ident.span),
    };
    Ok(fhir::VariantDef { def_id, params: vec![], fields, ret, span: variant.span, lifted: true })
}

// FIXME(nilehmann) this is wrong, we should lift generic predicates in the same `LiftCtxt` than
// then owned item to generate appropriate `FluxOwnerId`s
pub fn lift_generic_predicates(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<fhir::GenericPredicates, ErrorGuaranteed> {
    let def_id = owner_id.def_id;
    let generics = tcx.hir().get_generics(def_id).unwrap();
    LiftCtxt::new(tcx, sess, owner_id).lift_generic_predicates(generics)
}

pub fn lift_fn(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<fhir::FnInfo, ErrorGuaranteed> {
    let cx = LiftCtxt::new(tcx, sess, owner_id);

    let def_id = owner_id.def_id;
    let hir = tcx.hir();
    let hir_id = hir.local_def_id_to_hir_id(def_id);
    let fn_sig = hir
        .fn_sig_by_hir_id(hir_id)
        .expect("item does not have a `FnDecl`");
    let generics = tcx.hir().get_generics(def_id).unwrap();

    let fn_sig = cx.lift_fn_sig(fn_sig)?;
    let fn_preds = cx.lift_generic_predicates(generics)?;
    // FIXME(nilehmann) this only works for RPIT. We should generalize it for other `impl Trait` origins
    let opaque_tys = if tcx.hir().maybe_body_owned_by(def_id).is_some() {
        tcx.opaque_types_defined_by(def_id)
            .iter()
            .map(|opaque_ty_id| {
                let hir::ItemKind::OpaqueTy(opaque_ty) = hir.expect_item(*opaque_ty_id).kind else {
                    bug!("expected opaque type")
                };
                Ok((*opaque_ty_id, cx.lift_opaque_ty(opaque_ty)?))
            })
            .try_collect()?
    } else {
        FxHashMap::default()
    };
    Ok(fhir::FnInfo { fn_sig, fn_preds, opaque_tys })
}

pub fn lift_self_ty(
    tcx: TyCtxt,
    sess: &FluxSession,
    owner_id: OwnerId,
) -> Result<Option<fhir::Ty>, ErrorGuaranteed> {
    let cx = LiftCtxt::new(tcx, sess, owner_id);
    if let Some(def_id) = tcx.impl_of_method(owner_id.to_def_id()) {
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

        // FIXME(nilehmann) the span should also include the generic arguments
        let span = item.ident.span;
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
    fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession, owner: OwnerId) -> Self {
        Self { tcx, sess, local_id_gen: IndexGen::new(), owner }
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Rust(self.owner), local_id: self.local_id_gen.fresh() }
    }

    pub fn lift_generic_predicates(
        &self,
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
        &self,
        pred: &hir::WherePredicate,
    ) -> Result<fhir::WhereBoundPredicate, ErrorGuaranteed> {
        if let hir::WherePredicate::BoundPredicate(bound) = pred {
            if !bound.bound_generic_params.is_empty() {
                return self.emit_unsupported(&format!("unsupported where predicate: `{bound:?}`"));
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
        &self,
        bound: &hir::GenericBound,
    ) -> Result<fhir::GenericBound, ErrorGuaranteed> {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref, hir::TraitBoundModifier::None)
                if poly_trait_ref.bound_generic_params.is_empty() =>
            {
                Ok(fhir::GenericBound::Trait(
                    self.lift_path(poly_trait_ref.trait_ref.path)?,
                    fhir::TraitBoundModifier::None,
                ))
            }
            hir::GenericBound::Trait(poly_trait_ref, hir::TraitBoundModifier::Maybe)
                if poly_trait_ref.bound_generic_params.is_empty() =>
            {
                Ok(fhir::GenericBound::Trait(
                    self.lift_path(poly_trait_ref.trait_ref.path)?,
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

    fn lift_opaque_ty(&self, opaque_ty: &hir::OpaqueTy) -> Result<fhir::OpaqueTy, ErrorGuaranteed> {
        Ok(fhir::OpaqueTy {
            bounds: opaque_ty
                .bounds
                .iter()
                .map(|bound| self.lift_generic_bound(bound))
                .try_collect()?,
        })
    }

    fn lift_fn_sig(&self, fn_sig: &hir::FnSig) -> Result<fhir::FnSig, ErrorGuaranteed> {
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

    fn lift_fn_ret_ty(&self, ret_ty: &hir::FnRetTy) -> Result<fhir::Ty, ErrorGuaranteed> {
        match ret_ty {
            hir::FnRetTy::DefaultReturn(_) => {
                let kind = fhir::TyKind::Tuple(vec![]);
                Ok(fhir::Ty { kind, fhir_id: self.next_fhir_id(), span: ret_ty.span() })
            }
            hir::FnRetTy::Return(ty) => self.lift_ty(ty),
        }
    }

    fn lift_field_def(&self, field_def: &hir::FieldDef) -> Result<fhir::FieldDef, ErrorGuaranteed> {
        let ty = self.lift_ty(field_def.ty)?;
        Ok(fhir::FieldDef { def_id: field_def.def_id, ty, lifted: true })
    }

    fn lift_ty(&self, ty: &hir::Ty) -> Result<fhir::Ty, ErrorGuaranteed> {
        let kind = match &ty.kind {
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
                let args = self.lift_generic_args(args)?;
                fhir::TyKind::OpaqueDef(*item_id, args, *in_trait_def)
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
        let res = match lft.res {
            hir::LifetimeName::Param(def_id) => fhir::LifetimeRes::Param(def_id),
            hir::LifetimeName::Static => fhir::LifetimeRes::Static,
            hir::LifetimeName::ImplicitObjectLifetimeDefault
            | hir::LifetimeName::Error
            | hir::LifetimeName::Infer => {
                return self.emit_unsupported(&format!("unsupported lifetime: `{lft}`",));
            }
        };
        Ok(fhir::Lifetime { fhir_id: self.next_fhir_id(), ident: lft.ident, res })
    }

    fn lift_mut_ty(&self, mut_ty: &hir::MutTy) -> Result<fhir::MutTy, ErrorGuaranteed> {
        Ok(fhir::MutTy { ty: Box::new(self.lift_ty(mut_ty.ty)?), mutbl: mut_ty.mutbl })
    }

    fn lift_qpath(&self, qpath: &hir::QPath) -> Result<fhir::Ty, ErrorGuaranteed> {
        match qpath {
            hir::QPath::Resolved(self_ty, path) => self.lift_path_to_ty(*self_ty, path),
            hir::QPath::TypeRelative(_, _) | hir::QPath::LangItem(_, _, _) => {
                self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::qpath_to_string(qpath)
                ))
            }
        }
    }

    fn lift_path(&self, path: &hir::Path) -> Result<fhir::Path, ErrorGuaranteed> {
        let res = match path.res {
            hir::def::Res::Def(kind, def_id) => fhir::Res::Def(kind, def_id),
            hir::def::Res::PrimTy(prim_ty) => fhir::Res::PrimTy(prim_ty),
            hir::def::Res::SelfTyAlias { alias_to, is_trait_impl, forbid_generic: false } => {
                fhir::Res::SelfTyAlias { alias_to, is_trait_impl }
            }
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported type: `{}` {:?}",
                    rustc_hir_pretty::path_to_string(path),
                    path.res
                ));
            }
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
        &self,
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
        &self,
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
        &self,
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

    fn lift_array_len(&self, len: &hir::ArrayLen) -> Result<fhir::ArrayLen, ErrorGuaranteed> {
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
                    let lft = fhir::Lifetime {
                        fhir_id: self.next_fhir_id(),
                        ident: param.name.ident(),
                        res: fhir::LifetimeRes::Param(param.def_id),
                    };
                    args.push(fhir::GenericArg::Lifetime(lft));
                }
                hir::GenericParamKind::Const { .. } => {
                    return self.emit_unsupported("const generics are not supported");
                }
            }
        }
        Ok(args)
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
