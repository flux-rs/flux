use std::iter;

use flux_common::{bug, iter::IterExt};
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::{rty::ParamTy, rustc::ty::Mutability};
use flux_syntax::surface::{self, Res};
use hir::{def_id::DefId, HirId, OwnerId, PrimTy};
use itertools::Itertools;
use rustc_ast::LitKind;
use rustc_hash::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use surface::Ident;

pub fn resolve_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    struct_def: surface::StructDef,
) -> Result<surface::StructDef<Res>, ErrorGuaranteed> {
    let item = tcx.hir().expect_item(struct_def.def_id);
    let hir::ItemKind::Struct(hir_variant, _) = &item.kind else {
        bug!("expected struct");
    };
    let fields = if struct_def.opaque {
        vec![None; struct_def.fields.len()]
    } else {
        iter::zip(struct_def.fields, hir_variant.fields())
            .map(|(opt_ty, hir_field)| {
                let Some(ty) = opt_ty else {
                    return Ok(None)
                };
                let zipper = Zipper::new(tcx, sess, hir_field.def_id);
                let ty = zipper.zip_ty(ty, hir_field.ty)?;
                Ok(Some(ty))
            })
            .try_collect_exhaust()?
    };
    Ok(surface::StructDef {
        def_id: struct_def.def_id,
        fields,
        invariants: struct_def.invariants,
        opaque: struct_def.opaque,
        refined_by: struct_def.refined_by,
    })
}

pub fn resolve_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    enum_def: surface::EnumDef,
) -> Result<surface::EnumDef<Res>, ErrorGuaranteed> {
    let item = tcx.hir().expect_item(enum_def.def_id);
    let hir::ItemKind::Enum(hir_enum_def, _) = &item.kind else {
        bug!("expected enum");
    };
    let variants = iter::zip(enum_def.variants, hir_enum_def.variants)
        .map(|(variant, hir_variant)| {
            let zipper = Zipper::new(tcx, sess, hir_variant.def_id);
            zipper.zip_enum_variant(variant, hir_variant)
        })
        .try_collect_exhaust()?;

    Ok(surface::EnumDef {
        def_id: enum_def.def_id,
        refined_by: enum_def.refined_by,
        variants,
        invariants: enum_def.invariants,
    })
}

pub fn resolve_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: LocalDefId,
    fn_sig: surface::FnSig,
) -> Result<surface::FnSig<Res>, ErrorGuaranteed> {
    let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
    let hir_fn_decl = tcx
        .hir()
        .fn_decl_by_hir_id(hir_id)
        .expect("expected function decl");
    let mut zipper = Zipper::new(tcx, sess, def_id);
    let args = zipper.zip_fn_args(fn_sig.args, hir_fn_decl.inputs)?;
    let returns = zipper.zip_return_ty(fn_sig.returns, &hir_fn_decl.output)?;
    let ensures = zipper.zip_ensures(fn_sig.ensures)?;

    Ok(surface::FnSig {
        params: fn_sig.params,
        requires: fn_sig.requires,
        args,
        returns,
        ensures,
        span: fn_sig.span,
    })
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
        variant: surface::VariantDef,
        hir_variant: &hir::Variant,
    ) -> Result<surface::VariantDef<Res>, ErrorGuaranteed> {
        let flux_fields = variant.fields.len();
        let hir_fields = hir_variant.data.fields().len();
        if flux_fields != hir_fields {
            todo!("mismatch fields in variant");
        }

        let fields = iter::zip(variant.fields, hir_variant.data.fields())
            .map(|(ty, hir_field)| self.zip_ty(ty, hir_field.ty))
            .try_collect_exhaust()?;
        let ret = surface::VariantRet {
            path: self.zip_with_self_ty(variant.ret.path)?,
            indices: variant.ret.indices,
        };

        Ok(surface::VariantDef { fields, ret, span: variant.span })
    }

    fn zip_fn_args(
        &mut self,
        args: Vec<surface::Arg>,
        hir_tys: &'tcx [hir::Ty<'tcx>],
    ) -> Result<Vec<surface::Arg<Res>>, ErrorGuaranteed> {
        let flux_args = args.len();
        let hir_args = hir_tys.len();
        if flux_args != hir_args {
            todo!()
        }

        iter::zip(args, hir_tys)
            .map(|(arg, hir_ty)| self.zip_fn_arg(arg, hir_ty))
            .try_collect_exhaust()
    }

    fn zip_fn_arg(
        &mut self,
        arg: surface::Arg,
        hir_ty: &'tcx hir::Ty<'tcx>,
    ) -> Result<surface::Arg<Res>, ErrorGuaranteed> {
        match (arg, &hir_ty.kind) {
            (surface::Arg::Ty(ident, ty), _) => {
                Ok(surface::Arg::Ty(ident, self.zip_ty(ty, hir_ty)?))
            }
            (surface::Arg::Constr(bind, path, pred), hir::TyKind::Path(qpath)) => {
                Ok(surface::Arg::Constr(bind, self.zip_path(path, qpath)?, pred))
            }
            (
                surface::Arg::StrgRef(loc, ty),
                hir::TyKind::Ref(_, hir::MutTy { ty: hir_ty, mutbl: hir::Mutability::Mut }),
            ) => {
                self.locs.insert(loc, hir_ty);
                Ok(surface::Arg::StrgRef(loc, self.zip_ty(ty, hir_ty)?))
            }
            _ => todo!(),
        }
    }

    fn zip_return_ty(
        &self,
        ret_ty: Option<surface::Ty>,
        hir_ret_ty: &hir::FnRetTy,
    ) -> Result<Option<surface::Ty<Res>>, ErrorGuaranteed> {
        match (ret_ty, hir_ret_ty) {
            (None, hir::FnRetTy::DefaultReturn(_)) => Ok(None),
            (Some(ty), hir::FnRetTy::Return(hir_ty)) => Ok(Some(self.zip_ty(ty, hir_ty)?)),
            _ => todo!(),
        }
    }

    fn zip_ensures(
        &self,
        ensures: Vec<(surface::Ident, surface::Ty)>,
    ) -> Result<Vec<(surface::Ident, surface::Ty<Res>)>, ErrorGuaranteed> {
        ensures
            .into_iter()
            .map(|(loc, ty)| {
                let Some(hir_ty) = self.locs.get(&loc) else {
                    todo!()
                };
                let ty = self.zip_ty(ty, hir_ty)?;
                Ok((loc, ty))
            })
            .try_collect_exhaust()
    }

    fn zip_ty(
        &self,
        ty: surface::Ty,
        hir_ty: &hir::Ty,
    ) -> Result<surface::Ty<Res>, ErrorGuaranteed> {
        let kind = match (ty.kind, &hir_ty.kind) {
            (surface::TyKind::Base(bty), _) => surface::TyKind::Base(self.zip_bty(bty, hir_ty)?),
            (surface::TyKind::Indexed { bty, indices }, _) => {
                surface::TyKind::Indexed { bty: self.zip_bty(bty, hir_ty)?, indices }
            }
            (surface::TyKind::Exists { bind, bty, pred }, _) => {
                surface::TyKind::Exists { bind, bty: self.zip_bty(bty, hir_ty)?, pred }
            }
            (surface::TyKind::Constr(pred, ty), _) => {
                surface::TyKind::Constr(pred, Box::new(self.zip_ty(*ty, hir_ty)?))
            }
            (surface::TyKind::Ref(rk, ty), hir::TyKind::Ref(_, mut_ty)) => {
                self.mutability(rk, mut_ty.mutbl)?;
                surface::TyKind::Ref(rk, Box::new(self.zip_ty(*ty, mut_ty.ty)?))
            }
            (surface::TyKind::Tuple(tys), hir::TyKind::Tup(hir_tys)) => {
                let tys = iter::zip(tys, *hir_tys)
                    .map(|(ty, hir_ty)| self.zip_ty(ty, hir_ty))
                    .try_collect_exhaust()?;
                surface::TyKind::Tuple(tys)
            }
            (surface::TyKind::Array(ty, len), hir::TyKind::Array(hir_ty, hir_len)) => {
                self.array_len(len, *hir_len)?;
                surface::TyKind::Array(Box::new(self.zip_ty(*ty, hir_ty)?), len)
            }
            _ => {
                todo!()
            }
        };
        Ok(surface::Ty { kind, span: ty.span })
    }

    fn zip_bty(
        &self,
        bty: surface::BaseTy,
        hir_ty: &hir::Ty,
    ) -> Result<surface::BaseTy<Res>, ErrorGuaranteed> {
        match (bty, &hir_ty.kind) {
            (surface::BaseTy::Path(path), hir::TyKind::Path(qpath)) => {
                let path = self.zip_path(path, qpath)?;
                Ok(surface::BaseTy::Path(path))
            }
            (surface::BaseTy::Slice(ty), hir::TyKind::Slice(hir_ty)) => {
                Ok(surface::BaseTy::Slice(Box::new(self.zip_ty(*ty, hir_ty)?)))
            }
            (bty, _) => {
                todo!("\n{bty:?}\n{hir_ty:?}")
            }
        }
    }

    fn zip_path(
        &self,
        path: surface::Path,
        hir_path: &hir::QPath,
    ) -> Result<surface::Path<Res>, ErrorGuaranteed> {
        let hir_path = &SimplifiedHirPath::try_from(hir_path).map_err(|_| todo!())?;
        if let hir::def::Res::SelfTyAlias { .. } = hir_path.res {
            return self.zip_with_self_ty(path);
        }
        self.zip_path_segments(&path, hir_path)?;

        let res = match hir_path.res {
            hir::def::Res::Def(hir::def::DefKind::Struct | hir::def::DefKind::Enum, def_id) => {
                surface::Res::Adt(def_id)
            }
            hir::def::Res::Def(hir::def::DefKind::TyParam, def_id) => {
                surface::Res::Param(self.generics[def_id])
            }
            hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id) => {
                let ty = self.tcx.type_of(def_id);
                match res_from_ty(ty) {
                    Some(res) => res,
                    None => {
                        todo!()
                        // ResEntry::Unsupported {
                        //     span,
                        //     reason: format!("unsupported alias `{ty:?}`"),
                        // }
                    }
                }
            }
            hir::def::Res::PrimTy(PrimTy::Bool) => surface::Res::Bool,
            hir::def::Res::PrimTy(PrimTy::Char) => surface::Res::Char,
            hir::def::Res::PrimTy(PrimTy::Str) => surface::Res::Str,
            hir::def::Res::PrimTy(PrimTy::Float(float_ty)) => {
                surface::Res::Float(rustc_middle::ty::float_ty(float_ty))
            }
            hir::def::Res::PrimTy(PrimTy::Uint(uint_ty)) => {
                surface::Res::Uint(rustc_middle::ty::uint_ty(uint_ty))
            }
            hir::def::Res::PrimTy(PrimTy::Int(int_ty)) => {
                surface::Res::Int(rustc_middle::ty::int_ty(int_ty))
            }
            hir::def::Res::SelfTyAlias { alias_to, .. } => surface::Res::Adt(alias_to),
            hir::def::Res::SelfCtor(_)
            | hir::def::Res::SelfTyParam { .. }
            | hir::def::Res::Def(..)
            | hir::def::Res::Local(_)
            | hir::def::Res::ToolMod
            | hir::def::Res::NonMacroAttr(_)
            | hir::def::Res::Err => todo!("{:?}", hir_path.res),
        };
        let args = self.zip_generic_args(path.args, &hir_path.args)?;

        Ok(surface::Path { res, args, segments: path.segments, span: path.span })
    }

    fn zip_generic_args(
        &self,
        args: Vec<surface::Ty>,
        hir_args: &[&hir::Ty],
    ) -> Result<Vec<surface::Ty<Res>>, ErrorGuaranteed> {
        if args.len() != hir_args.len() {
            todo!("generic argument count mismatch {args:?} {hir_args:?}")
        }

        iter::zip(args, hir_args.iter())
            .map(|(arg, hir_arg)| self.zip_ty(arg, hir_arg))
            .try_collect_exhaust()
    }

    fn mutability(&self, rk: surface::RefKind, mutbl: Mutability) -> Result<(), ErrorGuaranteed> {
        match (rk, mutbl) {
            (surface::RefKind::Mut, Mutability::Mut) | (surface::RefKind::Shr, Mutability::Not) => {
                Ok(())
            }
            _ => {
                todo!("mutability mismatch")
                // Err(self.sess.emit_err(errors::MutabilityMismatch::new(
                //     self.tcx,
                //     span,
                //     self.def_id,
                // )))
            }
        }
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
            if len.val as u128 != hir_len {
                todo!("array length mismatch")
            }
            Ok(())
        } else {
            todo!("unsupported body")
        }
    }

    fn zip_path_segments(
        &self,
        path: &surface::Path,
        hir_path: &SimplifiedHirPath,
    ) -> Result<(), ErrorGuaranteed> {
        if path.segments.len() != hir_path.segments.len() {
            todo!("path segment mismatch {path:?} {hir_path:?}")
        }
        for (segment, hir_segment) in iter::zip(&path.segments, &hir_path.segments) {
            if segment != hir_segment {
                todo!("path segment mismatch {path:?} {hir_path:?}")
            }
        }
        Ok(())
    }

    fn zip_with_self_ty(&self, path: surface::Path) -> Result<surface::Path<Res>, ErrorGuaranteed> {
        let Some(self_ty) = self.self_ty.as_ref() else {
            todo!("no self type")
        };
        let &[ident] = &path.segments[..] else {
            todo!("path must have one segment");
        };
        if ident != self_ty.ident {
            todo!("ident must be the same than the self type");
        }
        if path.args.len() != self_ty.args.len() {
            todo!(
                "invalid number of generic args for variant ret path {:?} {:?}",
                path.args,
                self_ty.args
            );
        }

        let mut args = vec![];
        for (arg, hir_arg) in iter::zip(path.args, &self_ty.args) {
            if let surface::TyKind::Base(surface::BaseTy::Path(path)) = arg.kind
                && let &[arg_ident] = &path.segments[..]
                && path.args.is_empty()
                && arg_ident.name == hir_arg.name
            {
                let path = surface::Path {
                    segments: path.segments,
                    args: vec![],
                    res: Res::Param(*hir_arg),
                    span: path.span,
                };
                let kind = surface::TyKind::Base(surface::BaseTy::Path(path));
                args.push(surface::Ty { kind, span: arg.span });
            } else {
                todo!("variant ret path must be a type parameter");
            }
        }
        Ok(surface::Path {
            span: path.span,
            segments: vec![self_ty.ident],
            args,
            res: Res::Adt(self_ty.def_id.to_def_id()),
        })
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
