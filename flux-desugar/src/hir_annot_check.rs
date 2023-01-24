use std::iter;

use flux_common::{bug, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::{rty::ParamTy, rustc::ty::Mutability};
use flux_syntax::surface::{self, Res};
use hir::{def_id::DefId, HirId, OwnerId, PrimTy};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use surface::Ident;

pub fn check_struct_def(
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
        |(opt_ty, hir_field)| {
            if let Some(ty) = opt_ty {
                let zipper = Zipper::new(tcx, sess, hir_field.def_id);
                zipper.zip_ty(ty, hir_field.ty)?;
            }
            Ok(())
        },
    )
}

pub fn check_enum_def(
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
            let zipper = Zipper::new(tcx, sess, hir_variant.def_id);
            zipper.zip_enum_variant(variant, hir_variant)
        },
    )
}

pub fn check_fn_sig(
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
    let mut zipper = Zipper::new(tcx, sess, def_id);
    zipper.zip_fun_args(fn_sig.span, &fn_sig.args, hir_fn_decl.inputs)?;
    zipper.zip_return_ty(fn_sig.span, &fn_sig.returns, &hir_fn_decl.output)?;
    zipper.zip_ensures(&fn_sig.ensures)?;

    Ok(())
}

struct Zipper<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'sess FluxSession,
    generics: GenericsMap,
    self_ty: Option<SimplifiedSelfTy>,
    locs: LocsMap<'tcx>,
    /// [`LocalDefId`] of the definition being zipped, this could either be a field on a struct,
    /// a variant on a enum, or a function.
    def_id: LocalDefId,
}

#[derive(Debug)]
struct SimplifiedHirPath<'hir> {
    args: Vec<&'hir hir::Ty<'hir>>,
    segments: Vec<Ident>,
    res: hir::def::Res,
}

struct SimplifiedSelfTy {
    def_id: LocalDefId,
    ident: Ident,
    args: Vec<ParamTy>,
}

#[derive(Default)]
struct GenericsMap {
    map: FxHashMap<DefId, ParamTy>,
}

type LocsMap<'hir> = FxHashMap<Ident, &'hir hir::Ty<'hir>>;

impl<'sess, 'tcx> Zipper<'sess, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'sess FluxSession, def_id: LocalDefId) -> Self {
        // If we are zipping a field or a variant find the parent struct/enum to get its generics.
        let owner_id = as_owner_or_parent(tcx, def_id);
        let (self_ty, generics) = match tcx.hir().owner(owner_id) {
            hir::OwnerNode::Item(item) => {
                (SimplifiedSelfTy::try_from(item).ok(), GenericsMap::from(item))
            }
            hir::OwnerNode::ImplItem(impl_item) => {
                (self_ty_for_impl_item(tcx, impl_item), GenericsMap::from_impl_item(tcx, impl_item))
            }
            _ => bug!("expected a function or method"),
        };

        Self { tcx, sess, generics, self_ty, def_id, locs: LocsMap::default() }
    }

    fn zip_enum_variant(
        &self,
        variant: &surface::VariantDef<Res>,
        hir_variant: &hir::Variant,
    ) -> Result<(), ErrorGuaranteed> {
        let flux_fields = variant.fields.len();
        let hir_fields = hir_variant.data.fields().len();
        if flux_fields != hir_fields {
            todo!("mismatch fields in variant");
        }

        let fields = iter::zip(&variant.fields, hir_variant.data.fields())
            .try_for_each_exhaust(|(ty, hir_field)| self.zip_ty(ty, hir_field.ty))?;
        // let ret = surface::VariantRet {
        //     path: self.zip_with_self_ty(variant.ret.path)?,
        //     indices: variant.ret.indices,
        // };

        Ok(())

        // Ok(surface::VariantDef { fields, ret, span: variant.span })
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
            return Err(self.sess.emit_err(errors::ArgCountMismatch::new(
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
        match (arg, &hir_ty.kind) {
            (surface::Arg::Ty(_, ty), _) => self.zip_ty(ty, hir_ty),
            (surface::Arg::Constr(_, path, _), hir::TyKind::Path(qpath)) => {
                self.zip_path(path, qpath)
            }
            (
                surface::Arg::StrgRef(loc, ty),
                hir::TyKind::Ref(_, hir::MutTy { ty: hir_ty, mutbl: hir::Mutability::Mut }),
            ) => {
                self.locs.insert(*loc, hir_ty);
                self.zip_ty(ty, hir_ty)
            }
            _ => todo!(),
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
        ensures.into_iter().try_for_each_exhaust(|(loc, ty)| {
            let Some(hir_ty) = self.locs.get(&loc) else {
                    todo!()
                };
            self.zip_ty(ty, hir_ty)
        })
    }

    fn zip_ty(&self, ty: &surface::Ty<Res>, hir_ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match (&ty.kind, &hir_ty.kind) {
            (surface::TyKind::Base(bty), _)
            | (surface::TyKind::Indexed { bty, .. }, _)
            | (surface::TyKind::Exists { bty, .. }, _) => self.zip_bty(ty.span, bty, hir_ty),
            (surface::TyKind::Constr(_, ty), _) => self.zip_ty(ty, hir_ty),
            (surface::TyKind::Ref(rk, ref_ty), hir::TyKind::Ref(_, mut_ty)) => {
                if !matches!(
                    (rk, mut_ty.mutbl),
                    (surface::RefKind::Mut, Mutability::Mut)
                        | (surface::RefKind::Shr, Mutability::Not)
                ) {
                    return self.emit_err(errors::MutabilityMismatch::new(ty.span, hir_ty.span));
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
            _ => self.emit_err(errors::InvalidRefinement::new(ty.span, hir_ty.span)),
        }
    }

    fn zip_bty(
        &self,
        ty_span: Span,
        bty: &surface::BaseTy<Res>,
        hir_ty: &hir::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        match (bty, &hir_ty.kind) {
            (surface::BaseTy::Path(path), hir::TyKind::Path(qpath)) => self.zip_path(path, qpath),
            (surface::BaseTy::Slice(ty), hir::TyKind::Slice(hir_ty)) => self.zip_ty(ty, hir_ty),
            _ => self.emit_err(errors::InvalidRefinement::new(ty_span, hir_ty.span)),
        }
    }

    fn zip_path(
        &self,
        path: &surface::Path<Res>,
        hir_path: &hir::QPath,
    ) -> Result<(), ErrorGuaranteed> {
        let hir_path = &SimplifiedHirPath::try_from(hir_path).map_err(|_| todo!())?;
        if let hir::def::Res::SelfTyAlias { .. } = hir_path.res {
            todo!()
            // return self.zip_with_self_ty(path);
        }

        match (path.res, hir_path.res) {
            (
                surface::Res::Adt(def_id1),
                hir::def::Res::Def(hir::def::DefKind::Struct | hir::def::DefKind::Enum, def_id2),
            ) if def_id1 == def_id2 => {}
            (
                surface::Res::Param(ty_param),
                hir::def::Res::Def(hir::def::DefKind::TyParam, def_id),
            ) if self.generics[def_id] == ty_param => {}
            (_, hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id)) => {
                todo!()
            }
            (_, hir::def::Res::PrimTy(PrimTy::Bool)) => {}
            (_, hir::def::Res::PrimTy(PrimTy::Char)) => {}
            (_, hir::def::Res::PrimTy(PrimTy::Str)) => {}
            (_, hir::def::Res::PrimTy(PrimTy::Float(float_ty))) => {}
            (_, hir::def::Res::PrimTy(PrimTy::Uint(uint_ty))) => {}
            (_, hir::def::Res::PrimTy(PrimTy::Int(int_ty))) => {}
            (_, hir::def::Res::SelfTyAlias { alias_to, .. }) => {}
            (_, _) => todo!("{:?}", hir_path.res),
        };
        self.zip_generic_args(&path.args, &hir_path.args)
    }

    fn zip_generic_args(
        &self,
        args: &[surface::Ty<Res>],
        hir_args: &[&hir::Ty],
    ) -> Result<(), ErrorGuaranteed> {
        if args.len() != hir_args.len() {
            todo!("generic argument count mismatch {args:?} {hir_args:?}")
        }

        iter::zip(args, hir_args.iter())
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
            return self.emit_err(errors::UnsupportedHir::new(self.tcx, self.def_id, "only interger literals are supported for array lengths"))
        }
    }

    // fn zip_with_self_ty(&self, path: surface::Path) -> Result<surface::Path<Res>, ErrorGuaranteed> {
    //     let Some(self_ty) = self.self_ty.as_ref() else {
    //         todo!("no self type")
    //     };
    //     let &[ident] = &path.segments[..] else {
    //         todo!("path must have one segment");
    //     };
    //     if ident != self_ty.ident {
    //         todo!("ident must be the same than the self type");
    //     }
    //     if path.args.len() != self_ty.args.len() {
    //         todo!(
    //             "invalid number of generic args for variant ret path {:?} {:?}",
    //             path.args,
    //             self_ty.args
    //         );
    //     }

    //     let mut args = vec![];
    //     for (arg, hir_arg) in iter::zip(path.args, &self_ty.args) {
    //         if let surface::TyKind::Base(surface::BaseTy::Path(path)) = arg.kind
    //             && let &[arg_ident] = &path.segments[..]
    //             && path.args.is_empty()
    //             && arg_ident.name == hir_arg.name
    //         {
    //             let path = surface::Path {
    //                 segments: path.segments,
    //                 args: vec![],
    //                 res: Res::Param(*hir_arg),
    //                 span: path.span,
    //             };
    //             let kind = surface::TyKind::Base(surface::BaseTy::Path(path));
    //             args.push(surface::Ty { kind, span: arg.span });
    //         } else {
    //             todo!("variant ret path must be a type parameter");
    //         }
    //     }
    //     Ok(surface::Path {
    //         span: path.span,
    //         segments: vec![self_ty.ident],
    //         args,
    //         res: Res::Adt(self_ty.def_id.to_def_id()),
    //     })
    // }

    fn emit_err<'a, T>(&'a self, err: impl IntoDiagnostic<'a>) -> Result<T, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }
}

impl From<&hir::Item<'_>> for GenericsMap {
    fn from(item: &hir::Item) -> GenericsMap {
        let mut table = GenericsMap::default();
        if let Some(generics) = item.kind.generics() {
            table.insert(generics);
        }
        table
    }
}

impl GenericsMap {
    fn from_impl_item(tcx: TyCtxt, impl_item: &hir::ImplItem) -> GenericsMap {
        let mut table = GenericsMap::default();
        if let Some(parent_impl) = parent_impl(tcx, impl_item.hir_id()) {
            table.insert(parent_impl.generics);
        }
        table.insert(impl_item.generics);
        table
    }

    fn insert(&mut self, generics: &hir::Generics) {
        for (idx, param) in generics.params.iter().enumerate() {
            if let hir::GenericParamKind::Type { .. } = param.kind {
                let def_id = param.def_id.to_def_id();
                debug_assert!(!self.map.contains_key(&def_id));

                let name = param.name.ident().name;
                let param_ty = ParamTy { index: idx as u32, name };
                self.map.insert(def_id, param_ty);
            }
        }
    }
}

impl std::ops::Index<DefId> for GenericsMap {
    type Output = ParamTy;

    fn index(&self, did: DefId) -> &Self::Output {
        &self.map[&did]
    }
}

impl TryFrom<&hir::Item<'_>> for SimplifiedSelfTy {
    type Error = &'static str;

    fn try_from(item: &hir::Item) -> Result<SimplifiedSelfTy, &'static str> {
        let generics = item.kind.generics().expect("expected a struct or an enum");
        let args = generic_params_into_args(generics)?;
        Ok(SimplifiedSelfTy { ident: item.ident, args, def_id: item.owner_id.def_id })
    }
}

impl<'hir> TryFrom<&hir::QPath<'hir>> for SimplifiedHirPath<'hir> {
    type Error = &'static str;

    fn try_from(qpath: &hir::QPath<'hir>) -> Result<Self, &'static str> {
        let hir::QPath::Resolved(None, path) = qpath else {
            todo!("unsupported qpath")
        };

        let [prefix @ .., hir::PathSegment { ident, args, ..}] = path.segments else {
            bug!("empty path")
        };
        if prefix.iter().any(|segment| segment.args.is_some()) {
            todo!("path segments with generic arguments are not supported");
        }
        let mut filtered = vec![];
        if let Some(args) = args {
            for arg in args.args {
                match arg {
                    hir::GenericArg::Lifetime(_) => {}
                    hir::GenericArg::Type(ty) => filtered.push(*ty),
                    hir::GenericArg::Const(_) => {
                        todo!("const generic arguments are not supported")
                    }
                    hir::GenericArg::Infer(_) => {
                        todo!("infer generic arguments are not supported")
                    }
                }
            }
        }
        let mut segments = prefix.iter().map(|segment| segment.ident).collect_vec();
        segments.push(*ident);

        Ok(Self { args: filtered, segments, res: path.res })
    }
}

fn self_ty_for_impl_item(tcx: TyCtxt, impl_item: &hir::ImplItem) -> Option<SimplifiedSelfTy> {
    if let Some(parent_impl) = parent_impl(tcx, impl_item.hir_id())
        && let hir::TyKind::Path(qpath) = &parent_impl.self_ty.kind
        && let hir::QPath::Resolved(_, path) = qpath
        && let &[hir::PathSegment { ident, ..}] = path.segments
        && let hir::def::Res::Def(_, def_id) = path.res
        && let Some(def_id )= def_id.as_local()
    {
        let args = generic_params_into_args(parent_impl.generics).ok()?;
        Some(
            SimplifiedSelfTy {
                def_id,
                ident,
                args,
            }
        )
    } else {
        None
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

fn res_from_ty(ty: rustc_middle::ty::Ty) -> Option<Res> {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        TyKind::Bool => Some(Res::Bool),
        TyKind::Int(int_ty) => Some(Res::Int(*int_ty)),
        TyKind::Uint(uint_ty) => Some(Res::Uint(*uint_ty)),
        TyKind::Float(float_ty) => Some(Res::Float(*float_ty)),
        TyKind::Param(param_ty) => Some(Res::Param(*param_ty)),
        TyKind::Char => Some(Res::Char),
        _ => None,
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

fn generic_params_into_args(generics: &hir::Generics) -> Result<Vec<ParamTy>, &'static str> {
    let mut args = vec![];
    for (idx, param) in generics.params.iter().enumerate() {
        match param.kind {
            hir::GenericParamKind::Type { .. } => {
                let param_ty = ParamTy { index: idx as u32, name: param.name.ident().name };
                args.push(param_ty);
            }
            hir::GenericParamKind::Lifetime { .. } => {}
            hir::GenericParamKind::Const { .. } => {
                todo!("const generic parameters are not supported")
            }
        }
    }
    Ok(args)
}

mod errors {
    use flux_macros::{Diagnostic, Subdiagnostic};
    use rustc_hir::def_id::{DefId, LocalDefId};
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(hir_resolver::unsupported_hir, code = "FLUX")]
    #[note]
    pub(super) struct UnsupportedHir<'a> {
        #[primary_span]
        #[label]
        span: Span,
        def_kind: &'static str,
        note: &'a str,
    }

    impl<'a> UnsupportedHir<'a> {
        pub(super) fn new(tcx: TyCtxt, def_id: impl Into<DefId>, note: &'a str) -> Self {
            let def_id = def_id.into();
            let span = tcx
                .def_ident_span(def_id)
                .unwrap_or_else(|| tcx.def_span(def_id));
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Self { span, def_kind, note }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_resolver::array_len_mismatch, code = "FLUX")]
    pub(super) struct ArrayLenMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_len: usize,
        #[label(hir_resolver::hir_label)]
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
    #[diag(hir_resolver::expected_default_return, code = "FLUX")]
    pub(super) struct ExpectedDefaultReturn {
        #[primary_span]
        #[label]
        ret_ty_span: Span,
        #[label(hir_resolver::default_return)]
        default_ret_span: Span,
    }

    impl ExpectedDefaultReturn {
        pub(super) fn new(ret_ty_span: Span, default_ret_span: Span) -> Self {
            Self { ret_ty_span, default_ret_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_resolver::missing_return_type, code = "FLUX")]
    pub(super) struct MissingReturnType {
        #[primary_span]
        #[label]
        flux_sig_span: Span,
        #[label(hir_resolver::hir_ret)]
        rust_ret_ty_span: Span,
    }

    impl MissingReturnType {
        pub(super) fn new(flux_sig_span: Span, rust_ret_ty_span: Span) -> Self {
            Self { flux_sig_span, rust_ret_ty_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_resolver::invalid_refinement, code = "FLUX")]
    pub(super) struct InvalidRefinement {
        #[primary_span]
        #[label]
        flux_ty_span: Span,
        #[label(hir_resolver::hir_label)]
        hir_ty_span: Span,
    }

    impl InvalidRefinement {
        pub(super) fn new(flux_ty_span: Span, hir_ty_span: Span) -> Self {
            Self { flux_ty_span, hir_ty_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_resolver::mutability_mismatch, code = "FLUX")]
    pub struct MutabilityMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        #[label(hir_resolver::hir_label)]
        hir_span: Span,
    }

    impl MutabilityMismatch {
        pub fn new(flux_span: Span, hir_span: Span) -> Self {
            Self { flux_span, hir_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(hir_resolver::fun_arg_count_mismatch, code = "FLUX")]
    pub(super) struct ArgCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_args: usize,
        #[label(hir_resolver::hir_label)]
        hir_span: Span,
        hir_args: usize,
    }

    impl ArgCountMismatch {
        pub(super) fn new(
            flux_span: Span,
            flux_args: usize,
            hir_span: Span,
            hir_args: usize,
        ) -> Self {
            Self { flux_span, flux_args, hir_span, hir_args }
        }
    }
}
