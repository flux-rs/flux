//! "Lift" HIR types into  FHIR types.
//!
use fhir::FhirId;
use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use hir::{def::DefKind, def_id::DefId};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_errors::IntoDiagnostic;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use crate::fhir;

struct LiftCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    def_id: LocalDefId,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
}

pub fn lift_generics(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
) -> Result<fhir::Generics, ErrorGuaranteed> {
    let hir_generics = tcx.hir().get_generics(def_id).unwrap();
    let def_kind = tcx.def_kind(def_id.to_def_id());

    let cx = LiftCtxt::new(tcx, sess, def_id);

    let params = hir_generics
        .params
        .iter()
        .map(|param| {
            let kind = match param.kind {
                hir::GenericParamKind::Lifetime { .. } => fhir::GenericParamDefKind::Lifetime,
                hir::GenericParamKind::Type { default, .. } => {
                    match def_kind {
                        DefKind::AssocFn | DefKind::Fn | DefKind::Impl { .. } => {
                            debug_assert!(default.is_none());
                            fhir::GenericParamDefKind::BaseTy
                        }
                        _ => {
                            fhir::GenericParamDefKind::Type {
                                default: default.map(|ty| cx.lift_ty(ty)).transpose()?,
                            }
                        }
                    }
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

pub fn lift_refined_by(tcx: TyCtxt, def_id: LocalDefId) -> fhir::RefinedBy {
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
    def_id: LocalDefId,
) -> Result<fhir::TyAlias, ErrorGuaranteed> {
    let item = tcx.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(ty, _) = &item.kind else {
        bug!("expected type alias");
    };
    let cx = LiftCtxt::new(tcx, sess, def_id);
    let ty = cx.lift_ty(ty)?;
    Ok(fhir::TyAlias {
        def_id,
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
    let hir::Node::Field(field_def) = node else {
        bug!("expected a field")
    };
    let parent_id = tcx.hir().get_parent_item(hir_id);
    let ty = LiftCtxt::new(tcx, sess, parent_id.def_id).lift_ty(field_def.ty)?;
    Ok(fhir::FieldDef { def_id, ty, lifted: true })
}

pub fn lift_enum_variant_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
) -> Result<fhir::VariantDef, ErrorGuaranteed> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let node = tcx.hir().get(hir_id);
    let hir::Node::Variant(variant) = node else {
        bug!("expected a variant")
    };
    let enum_id = tcx.hir().get_parent_item(hir_id);
    let hir::OwnerNode::Item(hir::Item {
        ident,
        kind: hir::ItemKind::Enum(_, generics),
        ..
    }) = tcx.hir().owner(enum_id) else {
        bug!("expected an enum")
    };

    let cx = LiftCtxt::new(tcx, sess, def_id);

    let fields = variant
        .data
        .fields()
        .iter()
        .map(|field| cx.lift_ty(field.ty))
        .try_collect_exhaust()?;

    let path = fhir::Path {
        res: fhir::Res::Enum(enum_id.to_def_id()),
        generics: cx.generic_params_into_args(generics)?,
        refine: vec![],
        // FIXME(nilehmann) the span should also include the generic arguments
        span: ident.span,
    };
    let ret = fhir::VariantRet {
        bty: fhir::BaseTy::from(path),
        idx: fhir::RefineArg::Aggregate(enum_id.to_def_id(), vec![], ident.span, cx.next_fhir_id()),
    };
    Ok(fhir::VariantDef { def_id, params: vec![], fields, ret, span: variant.span, lifted: true })
}

pub fn lift_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let cx = LiftCtxt::new(tcx, sess, def_id);
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let fn_sig = tcx
        .hir()
        .fn_sig_by_hir_id(hir_id)
        .expect("item does not have a `FnDecl`");

    let args = fn_sig
        .decl
        .inputs
        .iter()
        .map(|ty| cx.lift_ty(ty))
        .try_collect_exhaust()?;

    let output = fhir::FnOutput {
        params: vec![],
        ensures: vec![],
        ret: cx.lift_fn_ret_ty(&fn_sig.decl.output)?,
    };

    Ok(fhir::FnSig {
        params: vec![],
        requires: vec![],
        args,
        output,
        lifted: true,
        span: fn_sig.span,
    })
}

impl<'a, 'tcx> LiftCtxt<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession, def_id: LocalDefId) -> Self {
        Self { tcx, sess, def_id, local_id_gen: IndexGen::new() }
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: self.def_id, local_id: self.local_id_gen.fresh() }
    }

    fn lift_fn_ret_ty(&self, ret_ty: &hir::FnRetTy) -> Result<fhir::Ty, ErrorGuaranteed> {
        match ret_ty {
            hir::FnRetTy::DefaultReturn(_) => {
                let kind = fhir::TyKind::Tuple(vec![]);
                Ok(fhir::Ty { kind, span: ret_ty.span() })
            }
            hir::FnRetTy::Return(ty) => self.lift_ty(ty),
        }
    }

    fn lift_ty(&self, ty: &hir::Ty) -> Result<fhir::Ty, ErrorGuaranteed> {
        let kind = match &ty.kind {
            hir::TyKind::Slice(ty) => {
                let kind = fhir::BaseTyKind::Slice(Box::new(self.lift_ty(ty)?));
                return Ok(fhir::BaseTy { kind, span: ty.span }.into());
            }
            hir::TyKind::Array(ty, len) => {
                fhir::TyKind::Array(Box::new(self.lift_ty(ty)?), self.lift_array_len(len)?)
            }
            hir::TyKind::Ref(_, mut_ty) => {
                fhir::TyKind::Ref(lift_mutability(mut_ty.mutbl), Box::new(self.lift_ty(mut_ty.ty)?))
            }
            hir::TyKind::Never => fhir::TyKind::Never,
            hir::TyKind::Tup(tys) => {
                fhir::TyKind::Tuple(tys.iter().map(|ty| self.lift_ty(ty)).try_collect()?)
            }
            hir::TyKind::Path(hir::QPath::Resolved(_, path)) => return self.lift_path(path),
            hir::TyKind::Ptr(mut_ty) => {
                fhir::TyKind::RawPtr(Box::new(self.lift_ty(mut_ty.ty)?), mut_ty.mutbl)
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

    fn lift_path(&self, path: &hir::Path) -> Result<fhir::Ty, ErrorGuaranteed> {
        let res = match path.res {
            hir::def::Res::Def(DefKind::Struct, def_id) => fhir::Res::Struct(def_id),
            hir::def::Res::Def(DefKind::Enum, def_id) => fhir::Res::Enum(def_id),
            hir::def::Res::Def(DefKind::TyAlias, def_id) => fhir::Res::Alias(def_id),
            hir::def::Res::PrimTy(prim_ty) => fhir::Res::PrimTy(prim_ty),
            hir::def::Res::Def(DefKind::TyParam, def_id) => fhir::Res::Param(def_id),
            hir::def::Res::SelfTyAlias { alias_to, .. } => {
                return self.lift_self_ty_alias(alias_to)
            }
            _ => {
                return self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::path_to_string(path)
                ));
            }
        };
        let path = fhir::Path {
            res,
            generics: self.lift_generic_args(path.segments.last().unwrap().args)?,
            refine: vec![],
            span: path.span,
        };
        Ok(fhir::BaseTy::from(path).into())
    }

    fn lift_self_ty_alias(&self, alias_to: DefId) -> Result<fhir::Ty, ErrorGuaranteed> {
        let hir = self.tcx.hir();
        let def_id = alias_to.expect_local();
        match hir.expect_item(def_id).kind {
            hir::ItemKind::Impl(parent_impl) => self.lift_ty(parent_impl.self_ty),
            _ => bug!("self types for structs and enums is not yet implemented"),
        }
    }

    fn lift_generic_args(
        &self,
        args: Option<&hir::GenericArgs>,
    ) -> Result<Vec<fhir::Ty>, ErrorGuaranteed> {
        let mut filtered = vec![];
        if let Some(args) = args {
            for arg in args.args {
                match arg {
                    hir::GenericArg::Lifetime(_) => {}
                    hir::GenericArg::Type(ty) => filtered.push(self.lift_ty(ty)?),
                    hir::GenericArg::Const(_) => {
                        return self.emit_unsupported("const generics are not supported")
                    }
                    hir::GenericArg::Infer(_) => {
                        bug!("unexpected inference generic argument");
                    }
                }
            }
        }
        Ok(filtered)
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
    ) -> Result<Vec<fhir::Ty>, ErrorGuaranteed> {
        let mut args = vec![];
        for param in generics.params.iter() {
            match param.kind {
                hir::GenericParamKind::Type { .. } => {
                    let res = fhir::Res::Param(param.def_id.to_def_id());
                    let path =
                        fhir::Path { res, generics: vec![], refine: vec![], span: param.span };
                    args.push(fhir::BaseTy::from(path).into());
                }
                hir::GenericParamKind::Lifetime { .. } => {}
                hir::GenericParamKind::Const { .. } => {
                    return self.emit_unsupported("const generics are not supported");
                }
            }
        }
        Ok(args)
    }

    fn emit_unsupported<T>(&self, msg: &str) -> Result<T, ErrorGuaranteed> {
        self.emit_err(errors::UnsupportedHir::new(self.tcx, self.def_id, msg))
    }

    fn emit_err<'b, T>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<T, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }
}

fn lift_mutability(mtbl: hir::Mutability) -> fhir::RefKind {
    match mtbl {
        hir::Mutability::Mut => fhir::RefKind::Mut,
        hir::Mutability::Not => fhir::RefKind::Shr,
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
