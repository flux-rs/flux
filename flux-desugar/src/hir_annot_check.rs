///! This module contains the logic to check flux annotations are valid refinements of the rust item
///! by checking against the types the hir.
use std::iter;

use flux_common::{bug, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::{fhir::lift::errors::UnsupportedHir, rustc::ty::Mutability};
use flux_syntax::surface::{self, Res};
use hir::{
    def::{DefKind, Res as HirRes},
    def_id::DefId,
    HirId, OwnerId,
};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use surface::Ident;

pub(crate) fn check_alias(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
    alias: &surface::TyAlias<Res>,
) -> Result<(), ErrorGuaranteed> {
    let item = tcx.hir().expect_item(def_id);
    let hir::ItemKind::TyAlias(hir_ty, _) = &item.kind else {
        bug!("expected type alias");
    };
    Zipper::new(tcx, sess, def_id)?.zip_ty(&alias.ty, hir_ty)
}

pub(crate) fn check_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    struct_def: &surface::StructDef<Res>,
) -> Result<(), ErrorGuaranteed> {
    if struct_def.opaque {
        return Ok(());
    }
    let item = tcx.hir().expect_item(struct_def.def_id);
    let hir::ItemKind::Struct(hir_variant, _) = &item.kind else {
        bug!("expected struct");
    };
    iter::zip(&struct_def.fields, hir_variant.fields()).try_for_each_exhaust(
        |(field, hir_field)| {
            if let Some(ty) = &field.ty {
                let zipper = Zipper::new(tcx, sess, hir_field.def_id)?;
                zipper.zip_ty(ty, hir_field.ty)?;
            }
            Ok(())
        },
    )
}

pub(crate) fn check_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    enum_def: &surface::EnumDef<Res>,
) -> Result<(), ErrorGuaranteed> {
    let item = tcx.hir().expect_item(enum_def.def_id);
    let hir::ItemKind::Enum(hir_enum_def, _) = &item.kind else {
        bug!("expected enum");
    };
    iter::zip(&enum_def.variants, hir_enum_def.variants).try_for_each_exhaust(
        |(variant, hir_variant)| {
            let zipper = Zipper::new(tcx, sess, hir_variant.def_id)?;
            zipper.zip_enum_variant(variant, hir_variant)
        },
    )
}

pub(crate) fn check_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
    fn_sig: &surface::FnSig<Res>,
) -> Result<(), ErrorGuaranteed> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let hir_fn_decl = tcx
        .hir()
        .fn_decl_by_hir_id(hir_id)
        .expect("expected function decl");
    let mut zipper = Zipper::new(tcx, sess, def_id)?;
    zipper.zip_fun_args(fn_sig.span, &fn_sig.args, hir_fn_decl.inputs)?;
    zipper.zip_return_ty(fn_sig.span, &fn_sig.returns, &hir_fn_decl.output)?;
    zipper.zip_ensures(&fn_sig.ensures)?;

    Ok(())
}

struct Zipper<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'sess FluxSession,
    self_ty: SelfTy<'tcx>,
    locs: LocsMap<'tcx>,
    /// [`LocalDefId`] of the definition being zipped, this could either be a field on a struct,
    /// a variant on a enum, or a function.
    def_id: LocalDefId,
}

#[derive(Debug)]
struct SimplifiedHirPath<'hir> {
    args: Vec<&'hir hir::Ty<'hir>>,
    span: Span,
    res: hir::def::Res,
}

enum SelfTy<'hir> {
    Adt { def_id: DefId, args: Vec<(DefId, Ident)>, span: Span, format: String },
    Impl(&'hir hir::Ty<'hir>, &'hir hir::QPath<'hir>),
}

type LocsMap<'hir> = FxHashMap<Ident, &'hir hir::Ty<'hir>>;

impl<'sess, 'tcx> Zipper<'sess, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        // If we are zipping a field or a variant find the parent struct/enum.
        let owner_id = as_owner_or_parent(tcx, def_id);
        let self_ty = SelfTy::from_owner(tcx, owner_id)
            .map_err(|err| sess.emit_err(UnsupportedHir::new(tcx, def_id, err)))?;
        Ok(Self { tcx, sess, self_ty, def_id, locs: LocsMap::default() })
    }

    fn zip_enum_variant(
        &self,
        variant_def: &surface::VariantDef<Res>,
        hir_variant: &hir::Variant,
    ) -> Result<(), ErrorGuaranteed> {
        let Some(data) = &variant_def.data else {
            return Ok(());
        };
        let flux_fields = data.fields.len();
        let hir_fields = hir_variant.data.fields().len();
        if flux_fields != hir_fields {
            return self.emit_err(errors::FieldCountMismatch::new(
                data.span,
                flux_fields,
                hir_variant.span,
                hir_fields,
            ));
        }

        iter::zip(&data.fields, hir_variant.data.fields())
            .try_for_each_exhaust(|(ty, hir_field)| self.zip_ty(ty, hir_field.ty))?;

        self.zip_with_self_ty(data.ret.path.span, &data.ret.path)?;

        Ok(())
    }

    fn zip_fun_args(
        &mut self,
        fn_sig_span: Span,
        args: &[surface::Arg<Res>],
        hir_tys: &'tcx [hir::Ty<'tcx>],
    ) -> Result<(), ErrorGuaranteed> {
        let flux_args = args.len();
        let hir_args = hir_tys.len();
        if flux_args != hir_args {
            return Err(self.sess.emit_err(errors::FunArgCountMismatch::new(
                fn_sig_span,
                flux_args,
                self.tcx.def_span(self.def_id),
                hir_args,
            )));
        }

        iter::zip(args, hir_tys).try_for_each_exhaust(|(arg, hir_ty)| self.zip_fun_arg(arg, hir_ty))
    }

    fn zip_fun_arg(
        &mut self,
        arg: &surface::Arg<Res>,
        hir_ty: &'tcx hir::Ty<'tcx>,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(_, path, pred) => {
                if let hir::TyKind::Path(hir_path) = &hir_ty.kind {
                    self.zip_path(path.span, path, hir_ty, hir_path)
                } else {
                    let span = path.span.to(pred.span);
                    self.emit_err(errors::InvalidRefinement::from_hir_ty(span, hir_ty))
                }
            }
            surface::Arg::Ty(_, ty) => self.zip_ty(ty, hir_ty),
            surface::Arg::StrgRef(loc, ty) => {
                if let hir::TyKind::Ref(_, hir::MutTy { ty: hir_ty, mutbl: hir::Mutability::Mut }) =
                    &hir_ty.kind
                {
                    self.locs.insert(*loc, hir_ty);
                    self.zip_ty(ty, hir_ty)
                } else {
                    let span = loc.span.to(ty.span);
                    self.emit_err(
                        errors::InvalidRefinement::from_hir_ty(span, hir_ty).with_note(
                            "only mutable reference can be refined with a strong reference",
                        ),
                    )
                }
            }
        }
    }

    fn zip_return_ty(
        &self,
        fn_sig_span: Span,
        ret_ty: &Option<surface::Ty<Res>>,
        hir_ret_ty: &hir::FnRetTy,
    ) -> Result<(), ErrorGuaranteed> {
        match (ret_ty, hir_ret_ty) {
            (None, hir::FnRetTy::DefaultReturn(_)) => Ok(()),
            (Some(ty), hir::FnRetTy::Return(hir_ty)) => self.zip_ty(ty, hir_ty),
            (Some(ty), hir::FnRetTy::DefaultReturn(default_ret_span)) => {
                self.emit_err(errors::ExpectedDefaultReturn::new(ty.span, *default_ret_span))
            }
            (None, hir::FnRetTy::Return(hir_ty)) => {
                self.emit_err(errors::MissingReturnType::new(fn_sig_span, hir_ty.span))
            }
        }
    }

    fn zip_ensures(
        &self,
        ensures: &[(surface::Ident, surface::Ty<Res>)],
    ) -> Result<(), ErrorGuaranteed> {
        ensures.iter().try_for_each_exhaust(|(loc, ty)| {
            if let Some(hir_ty) = self.locs.get(loc) {
                self.zip_ty(ty, hir_ty)
            } else {
                self.emit_err(errors::UnresolvedLocation::new(*loc))
            }
        })
    }

    fn zip_ty(&self, ty: &surface::Ty<Res>, hir_ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match (&ty.kind, &hir_ty.kind) {
            (surface::TyKind::Base(bty), _)
            | (surface::TyKind::Indexed { bty, .. }, _)
            | (surface::TyKind::Exists { bty, .. }, _) => self.zip_bty(ty, bty, hir_ty),
            (surface::TyKind::Constr(_, ty), _) => self.zip_ty(ty, hir_ty),
            (surface::TyKind::Ref(rk, ref_ty), hir::TyKind::Ref(_, mut_ty)) => {
                if !matches!(
                    (rk, mut_ty.mutbl),
                    (surface::RefKind::Mut, Mutability::Mut)
                        | (surface::RefKind::Shr, Mutability::Not)
                ) {
                    return self.emit_err(
                        errors::InvalidRefinement::from_hir_ty(ty.span, hir_ty)
                            .with_note("types differ in mutability"),
                    );
                }

                self.zip_ty(ref_ty, mut_ty.ty)
            }
            (surface::TyKind::Tuple(tys), hir::TyKind::Tup(hir_tys)) => {
                iter::zip(tys, *hir_tys)
                    .try_for_each_exhaust(|(ty, hir_ty)| self.zip_ty(ty, hir_ty))
            }
            (surface::TyKind::Array(ty, len), hir::TyKind::Array(hir_ty, hir_len)) => {
                self.array_len(*len, *hir_len)?;
                self.zip_ty(ty, hir_ty)
            }
            _ => self.emit_err(errors::InvalidRefinement::from_hir_ty(ty.span, hir_ty)),
        }
    }

    fn zip_bty(
        &self,
        ty: &surface::Ty<Res>,
        bty: &surface::BaseTy<Res>,
        hir_ty: &hir::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        match (bty, &hir_ty.kind) {
            (surface::BaseTy::Path(path, _), hir::TyKind::Path(qpath)) => {
                self.zip_path(ty.span, path, hir_ty, qpath)
            }
            (surface::BaseTy::Slice(ty), hir::TyKind::Slice(hir_ty)) => self.zip_ty(ty, hir_ty),
            _ => self.emit_err(errors::InvalidRefinement::from_hir_ty(ty.span, hir_ty)),
        }
    }

    fn zip_path(
        &self,
        ty_span: Span,
        path: &surface::Path<Res>,
        hir_ty: &hir::Ty,
        hir_path: &hir::QPath,
    ) -> Result<(), ErrorGuaranteed> {
        let hir_path = &SimplifiedHirPath::try_from(hir_path).map_err(|err| {
            self.sess
                .emit_err(UnsupportedHir::new(self.tcx, self.def_id, err))
        })?;

        match (path.res, hir_path.res) {
            (_, HirRes::SelfTyAlias { .. }) => self.zip_with_self_ty(ty_span, path),
            (Res::Adt(def_id1), HirRes::Def(DefKind::Struct | DefKind::Enum, def_id2))
                if def_id1 == def_id2 =>
            {
                self.zip_generic_args(def_id1, path, hir_path)
            }
            (Res::Alias(def_id1), HirRes::Def(DefKind::TyAlias, def_id2)) if def_id1 == def_id2 => {
                self.zip_generic_args(def_id1, path, hir_path)
            }
            (Res::Param(def_id1), HirRes::Def(DefKind::TyParam, def_id2)) if def_id1 == def_id2 => {
                // TODO(nilehmann) report an error if type parameter is used with generic arguments
                Ok(())
            }
            (Res::PrimTy(prim_ty1), HirRes::PrimTy(prim_ty2)) if prim_ty1 == prim_ty2 => {
                // TODO(nilehmann) report an error if primitive type is used with generic arguments
                Ok(())
            }
            _ => self.emit_err(errors::InvalidRefinement::from_hir_ty(ty_span, hir_ty)),
        }
    }

    fn zip_generic_args(
        &self,
        def_id: DefId,
        path: &surface::Path<Res>,
        hir_path: &SimplifiedHirPath,
    ) -> Result<(), ErrorGuaranteed> {
        let found = path.args.len();
        let expected = hir_path.args.len();
        if found != expected {
            return self.emit_err(errors::GenericArgCountMismatch::from_hir_path(
                self.tcx, def_id, path, hir_path,
            ));
        }

        iter::zip(&path.args, &hir_path.args)
            .try_for_each_exhaust(|(arg, hir_arg)| self.zip_ty(arg, hir_arg))
    }

    fn array_len(
        &self,
        len: surface::ArrayLen,
        hir_len: hir::ArrayLen,
    ) -> Result<(), ErrorGuaranteed> {
        let body = match hir_len {
            hir::ArrayLen::Body(anon_const) => self.tcx.hir().body(anon_const.body),
            hir::ArrayLen::Infer(_, _) => bug!("unexpected `ArrayLen::Infer`"),
        };
        if let hir::ExprKind::Lit(lit) = &body.value.kind
            && let LitKind::Int(hir_len, _) = lit.node
        {
            if len.val != hir_len as usize {
                return self.emit_err(errors::ArrayLenMismatch::new(len.span, len.val, lit.span, hir_len as usize));
            }
            Ok(())
        } else {
            return self.emit_err(UnsupportedHir::new(self.tcx, self.def_id, "only interger literals are supported for array lengths"))
        }
    }

    fn zip_with_self_ty(
        &self,
        ty_span: Span,
        path: &surface::Path<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        match &self.self_ty {
            SelfTy::Impl(ty, qpath) => self.zip_path(ty_span, path, ty, qpath),
            SelfTy::Adt { def_id, args, span, .. } => {
                if let Res::Adt(adt_def_id) = path.res && adt_def_id == *def_id {} else {
                    return self.emit_err(errors::InvalidRefinement::from_self_ty(path.span, &self.self_ty));
                };

                if path.args.len() != args.len() {
                    return self.emit_err(errors::GenericArgCountMismatch::new(
                        self.tcx,
                        *def_id,
                        path,
                        args.len(),
                        *span,
                    ));
                }

                for (arg, param_ty2) in iter::zip(&path.args, args) {
                    if let surface::TyKind::Base(surface::BaseTy::Path(path, _)) = &arg.kind
                        && let Res::Param(param_def_id) = path.res
                        && param_def_id == param_ty2.0
                    {
                        continue;
                    }
                    return self.emit_err(errors::InvalidRefinement::from_self_ty_generic_arg(
                        arg.span, *param_ty2,
                    ));
                }
                Ok(())
            }
        }
    }

    fn emit_err<'a, T>(&'a self, err: impl IntoDiagnostic<'a>) -> Result<T, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }
}

impl<'hir> SelfTy<'hir> {
    fn from_owner(tcx: TyCtxt<'hir>, owner_id: OwnerId) -> Result<Self, &'static str> {
        match tcx.hir().owner(owner_id) {
            hir::OwnerNode::Item(item) => Self::try_from(item),
            hir::OwnerNode::ImplItem(impl_item) => Self::from_impl_item(tcx, impl_item),
            _ => Err("expected item or impl_item"),
        }
    }

    fn from_impl_item(tcx: TyCtxt<'hir>, impl_item: &hir::ImplItem) -> Result<Self, &'static str> {
        if let Some(parent_impl) = parent_impl(tcx, impl_item.hir_id()) {
            match &parent_impl.self_ty.kind {
                hir::TyKind::Path(qpath) => Ok(Self::Impl(parent_impl.self_ty, qpath)),
                _ => Err("expected path"),
            }
        } else {
            Err("no parent impl")
        }
    }

    fn generic_params_into_args(
        generics: &hir::Generics,
    ) -> Result<Vec<(DefId, Ident)>, &'static str> {
        let mut args = vec![];
        for param in generics.params.iter() {
            match param.kind {
                hir::GenericParamKind::Type { .. } => {
                    args.push((param.def_id.to_def_id(), param.name.ident()));
                }
                hir::GenericParamKind::Lifetime { .. } => {}
                hir::GenericParamKind::Const { .. } => {
                    return Err("const generic are not supported")
                }
            }
        }
        Ok(args)
    }
}

impl<'hir> TryFrom<&hir::Item<'_>> for SelfTy<'hir> {
    type Error = &'static str;

    fn try_from(item: &hir::Item) -> Result<Self, &'static str> {
        let generics = item.kind.generics().expect("expected a struct or an enum");
        let args = Self::generic_params_into_args(generics)?;
        let format = format!(
            "{}<{}>",
            item.ident,
            args.iter()
                .format_with(", ", |arg, f| f(&format_args!("{}", arg.1)))
        );
        Ok(SelfTy::Adt { args, def_id: item.owner_id.to_def_id(), span: item.ident.span, format })
    }
}

impl<'hir> TryFrom<&hir::QPath<'hir>> for SimplifiedHirPath<'hir> {
    type Error = &'static str;

    fn try_from(qpath: &hir::QPath<'hir>) -> Result<Self, &'static str> {
        let hir::QPath::Resolved(None, path) = qpath else {
            return Err("unsupported qualified path `{qpath:?}`")
        };

        let [prefix @ .., hir::PathSegment { ident, args, ..}] = path.segments else {
            bug!("empty path")
        };
        if prefix.iter().any(|segment| segment.args.is_some()) {
            return Err("path segments with generic arguments are not supported");
        }
        let mut filtered = vec![];
        if let Some(args) = args {
            for arg in args.args {
                match arg {
                    hir::GenericArg::Lifetime(_) => {}
                    hir::GenericArg::Type(ty) => filtered.push(*ty),
                    hir::GenericArg::Const(_) => return Err("const generic are not supported"),
                    hir::GenericArg::Infer(_) => {
                        bug!("unexpected inference generic argument");
                    }
                }
            }
        }
        let mut segments = prefix.iter().map(|segment| segment.ident).collect_vec();
        segments.push(*ident);

        Ok(Self { args: filtered, res: path.res, span: path.span })
    }
}

fn parent_impl(tcx: TyCtxt, hir_id: HirId) -> Option<&hir::Impl> {
    let hir = tcx.hir();
    let parent_id = hir.get_parent_item(hir_id);
    if let hir::OwnerNode::Item(parent_item) = tcx.hir().owner(parent_id)
        && let hir::ItemKind::Impl(parent_impl) = &parent_item.kind
    {
        Some(*parent_impl)
    } else {
        None
    }
}

fn as_owner_or_parent(tcx: TyCtxt, def_id: LocalDefId) -> OwnerId {
    let hir = tcx.hir();
    let hir_id = hir.local_def_id_to_hir_id(def_id);
    if let Some(owner_id) = hir_id.as_owner() {
        owner_id
    } else {
        hir.get_parent_item(hir_id)
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use rustc_hir as hir;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    use super::{SelfTy, SimplifiedHirPath};

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::array_len_mismatch, code = "FLUX")]
    pub(super) struct ArrayLenMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_len: usize,
        #[label(hir_annot_check::hir_label)]
        hir_span: Span,
        hir_len: usize,
    }

    impl ArrayLenMismatch {
        pub(super) fn new(
            flux_span: Span,
            flux_len: usize,
            hir_span: Span,
            hir_len: usize,
        ) -> Self {
            Self { flux_span, flux_len, hir_span, hir_len }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::expected_default_return, code = "FLUX")]
    pub(super) struct ExpectedDefaultReturn {
        #[primary_span]
        #[label]
        ret_ty_span: Span,
        #[label(hir_annot_check::default_return)]
        default_ret_span: Span,
    }

    impl ExpectedDefaultReturn {
        pub(super) fn new(ret_ty_span: Span, default_ret_span: Span) -> Self {
            Self { ret_ty_span, default_ret_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::missing_return_type, code = "FLUX")]
    pub(super) struct MissingReturnType {
        #[primary_span]
        #[label]
        flux_sig_span: Span,
        #[label(hir_annot_check::hir_ret)]
        rust_ret_ty_span: Span,
    }

    impl MissingReturnType {
        pub(super) fn new(flux_sig_span: Span, rust_ret_ty_span: Span) -> Self {
            Self { flux_sig_span, rust_ret_ty_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::invalid_refinement, code = "FLUX")]
    pub(super) struct InvalidRefinement {
        #[primary_span]
        #[label]
        flux_span: Span,
        #[label(hir_annot_check::hir_label)]
        hir_span: Span,
        hir_type: String,
        #[note]
        has_note: Option<()>,
        note: String,
    }

    impl InvalidRefinement {
        pub(super) fn from_hir_ty(flux_span: Span, hir_ty: &hir::Ty) -> Self {
            let hir_type = rustc_hir_pretty::ty_to_string(hir_ty);
            Self {
                flux_span,
                hir_span: hir_ty.span,
                hir_type,
                has_note: None,
                note: "".to_string(),
            }
        }

        pub(super) fn from_self_ty(flux_span: Span, self_ty: &SelfTy) -> Self {
            match self_ty {
                SelfTy::Adt { span, format, .. } => {
                    Self {
                        flux_span,
                        hir_span: *span,
                        hir_type: format.clone(),
                        has_note: None,
                        note: "".to_string(),
                    }
                }
                SelfTy::Impl(ty, _) => Self::from_hir_ty(flux_span, ty),
            }
        }

        pub(super) fn from_self_ty_generic_arg(flux_span: Span, param_ty: (DefId, Ident)) -> Self {
            Self {
                flux_span,
                hir_span: param_ty.1.span,
                hir_type: param_ty.1.name.to_string(),
                has_note: None,
                note: "".to_string(),
            }
        }

        pub(super) fn with_note(self, note: impl ToString) -> Self {
            Self { has_note: Some(()), note: note.to_string(), ..self }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::fun_arg_count_mismatch, code = "FLUX")]
    pub(super) struct FunArgCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_args: usize,
        #[label(hir_annot_check::hir_label)]
        hir_span: Span,
        hir_args: usize,
    }

    impl FunArgCountMismatch {
        pub(super) fn new(
            flux_span: Span,
            flux_args: usize,
            hir_span: Span,
            hir_args: usize,
        ) -> Self {
            Self { flux_span, flux_args, hir_span, hir_args }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::unresolved_location, code = "FLUX")]
    pub(super) struct UnresolvedLocation {
        #[primary_span]
        #[label]
        span: Span,
        loc: Ident,
    }

    impl UnresolvedLocation {
        pub(super) fn new(ident: Ident) -> Self {
            Self { span: ident.span, loc: ident }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::field_count_mismatch, code = "FLUX")]
    pub(super) struct FieldCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_fields: usize,
        #[label(hir_annot_check::hir_label)]
        hir_span: Span,
        hir_fields: usize,
    }

    impl FieldCountMismatch {
        pub(super) fn new(
            flux_span: Span,
            flux_fields: usize,
            hir_span: Span,
            hir_fields: usize,
        ) -> Self {
            Self { flux_span, flux_fields, hir_span, hir_fields }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_annot_check::generic_argument_count_mismatch, code = "FLUX")]
    pub(super) struct GenericArgCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        expected: usize,
        found: usize,
        def_kind: &'static str,
        #[label(hir_annot_check::hir_label)]
        hir_span: Span,
    }

    impl GenericArgCountMismatch {
        pub(super) fn new<T>(
            tcx: TyCtxt,
            def_id: DefId,
            flux_path: &surface::Path<T>,
            expected: usize,
            hir_span: Span,
        ) -> Self {
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            let found = flux_path.args.len();
            let flux_span = flux_path.span;
            GenericArgCountMismatch { flux_span, expected, found, def_kind, hir_span }
        }

        pub(super) fn from_hir_path<T>(
            tcx: TyCtxt,
            def_id: DefId,
            flux_path: &surface::Path<T>,
            hir_path: &SimplifiedHirPath,
        ) -> Self {
            Self::new(tcx, def_id, flux_path, hir_path.args.len(), hir_path.span)
        }
    }
}
