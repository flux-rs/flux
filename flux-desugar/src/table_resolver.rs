use flux_common::{bug, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::fhir::Res;
use flux_syntax::surface::{self, BaseTy, BaseTyKind, Ident, Path, Ty};
use hir::{ItemKind, PathSegment};
use itertools::Itertools;
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub struct Resolver<'genv> {
    sess: &'genv FluxSession,
    table: NameResTable<'genv>,
}

#[derive(Hash, Eq, PartialEq)]
pub struct ResKey {
    s: String,
}

struct NameResTable<'sess> {
    res: FxHashMap<ResKey, ResEntry>,
    sess: &'sess FluxSession,
}

enum ResEntry {
    Res(Res),
    Unsupported { reason: String, span: Span },
}

impl<'sess> Resolver<'sess> {
    pub(crate) fn new(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let table = match tcx.def_kind(def_id) {
            hir::def::DefKind::Struct
            | hir::def::DefKind::Enum
            | hir::def::DefKind::Fn
            | hir::def::DefKind::TyAlias => NameResTable::from_item(tcx, sess, def_id)?,
            hir::def::DefKind::AssocFn => NameResTable::from_impl_item(tcx, sess, def_id)?,
            kind => bug!("unsupported kind {kind:?}"),
        };

        Ok(Self { sess, table })
    }

    pub(crate) fn resolve_type_alias(
        &self,
        alias_def: surface::TyAlias,
    ) -> Result<surface::TyAlias<Res>, ErrorGuaranteed> {
        let ty = self.resolve_ty(alias_def.ty)?;

        Ok(surface::TyAlias {
            ident: alias_def.ident,
            generics: alias_def.generics,
            refined_by: alias_def.refined_by,
            ty,
            span: alias_def.span,
        })
    }

    pub(crate) fn resolve_struct_def(
        &self,
        struct_def: surface::StructDef,
    ) -> Result<surface::StructDef<Res>, ErrorGuaranteed> {
        let fields = struct_def
            .fields
            .into_iter()
            .map(|ty| ty.map(|ty| self.resolve_ty(ty)).transpose())
            .try_collect_exhaust()?;

        Ok(surface::StructDef {
            refined_by: struct_def.refined_by,
            fields,
            opaque: struct_def.opaque,
            invariants: struct_def.invariants,
        })
    }

    pub(crate) fn resolve_enum_def(
        &self,
        enum_def: surface::EnumDef,
    ) -> Result<surface::EnumDef<Res>, ErrorGuaranteed> {
        let variants = enum_def
            .variants
            .into_iter()
            .map(|variant| self.resolve_variant(variant))
            .try_collect_exhaust()?;

        Ok(surface::EnumDef {
            refined_by: enum_def.refined_by,
            invariants: enum_def.invariants,
            variants,
        })
    }

    fn resolve_variant(
        &self,
        variant_def: Option<surface::VariantDef>,
    ) -> Result<Option<surface::VariantDef<Res>>, ErrorGuaranteed> {
        let variant_def = if let Some(variant_def) = variant_def {
            let fields = variant_def
                .fields
                .into_iter()
                .map(|ty| self.resolve_ty(ty))
                .try_collect_exhaust()?;
            let ret = self.resolve_variant_ret(variant_def.ret)?;
            Some(surface::VariantDef { fields, ret, span: variant_def.span })
        } else {
            None
        };
        Ok(variant_def)
    }

    fn resolve_variant_ret(
        &self,
        ret: surface::VariantRet,
    ) -> Result<surface::VariantRet<Res>, ErrorGuaranteed> {
        let path = self.resolve_path(ret.path)?;
        Ok(surface::VariantRet { path, indices: ret.indices })
    }

    // fn resolve_projection_predicate(
    //     &self,
    //     bound: surface::ProjectionPredicate,
    // ) -> Result<surface::ProjectionPredicate<Res>, ErrorGuaranteed> {
    //     let item = self.resolve_path(bound.item)?;
    //     let term = self.resolve_ty(bound.term)?;
    //     Ok(surface::ProjectionPredicate { item, term })
    // }

    // fn resolve_generic_bound(
    //     &self,
    //     bound: surface::GenericBound,
    // ) -> Result<surface::GenericBound<Res>, ErrorGuaranteed> {
    //     match bound {
    //         surface::GenericBound::Projection(pred) => {
    //             let pred = self.resolve_projection_predicate(pred)?;
    //             Ok(surface::GenericBound::Projection(pred))
    //         }
    //     }
    // }

    fn resolve_where_bound_predicate(
        &self,
        pred: surface::WhereBoundPredicate,
    ) -> Result<surface::WhereBoundPredicate<Res>, ErrorGuaranteed> {
        let bounded_ty = self.resolve_ty(pred.bounded_ty)?;
        let bounds = pred
            .bounds
            .into_iter()
            .map(|bound| self.resolve_path(bound))
            .try_collect_exhaust()?;
        Ok(surface::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
    }

    #[allow(dead_code)]
    pub(crate) fn resolve_fn_sig(
        &self,
        fn_sig: surface::FnSig,
    ) -> Result<surface::FnSig<Res>, ErrorGuaranteed> {
        let args = fn_sig
            .args
            .into_iter()
            .map(|arg| self.resolve_arg(arg))
            .try_collect_exhaust();

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(loc, ty)| Ok((loc, self.resolve_ty(ty)?)))
            .try_collect_exhaust();

        let predicates = fn_sig
            .predicates
            .into_iter()
            .map(|pred| {
                let pred = self.resolve_where_bound_predicate(pred)?;
                Ok(pred)
            })
            .try_collect_exhaust();

        let returns = fn_sig.returns.map(|ty| self.resolve_ty(ty)).transpose();

        Ok(surface::FnSig {
            params: fn_sig.params,
            requires: fn_sig.requires,
            args: args?,
            returns: returns?,
            ensures: ensures?,
            predicates: predicates?,
            span: fn_sig.span,
        })
    }

    fn resolve_arg(&self, arg: surface::Arg) -> Result<surface::Arg<Res>, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                Ok(surface::Arg::Constr(bind, self.resolve_path(path)?, pred))
            }
            surface::Arg::StrgRef(loc, ty) => Ok(surface::Arg::StrgRef(loc, self.resolve_ty(ty)?)),
            surface::Arg::Ty(bind, ty) => Ok(surface::Arg::Ty(bind, self.resolve_ty(ty)?)),
        }
    }

    fn resolve_ty(&self, ty: Ty) -> Result<Ty<Res>, ErrorGuaranteed> {
        let kind = match ty.kind {
            surface::TyKind::Base(bty) => {
                if let BaseTyKind::Path(path) = &bty.kind && path.is_hole() {
                    surface::TyKind::Hole
                } else {
                    surface::TyKind::Base(self.resolve_bty(bty)?)
                }
            },
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.resolve_bty(bty)?;
                surface::TyKind::Indexed { bty, indices }
            }
            surface::TyKind::Exists { bind, bty, pred } => {
                let bty = self.resolve_bty(bty)?;
                surface::TyKind::Exists { bind, bty, pred }
            }
            surface::TyKind::GeneralExists { params, ty, pred } => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::GeneralExists { params, ty: Box::new(ty), pred }
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Ref(mutbl, Box::new(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .into_iter()
                    .map(|ty| self.resolve_ty(ty))
                    .try_collect_exhaust()?;
                surface::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.resolve_ty(*ty)?;
                surface::TyKind::Array(Box::new(ty), len)
            }
            surface::TyKind::Hole => surface::TyKind::Hole,
        };
        Ok(surface::Ty { kind, span: ty.span })
    }

    fn resolve_bty(&self, bty: BaseTy) -> Result<BaseTy<Res>, ErrorGuaranteed> {
        let kind = match bty.kind {
            BaseTyKind::Path(path) => BaseTyKind::Path(self.resolve_path(path)?),
            BaseTyKind::Slice(ty) => {
                let ty = self.resolve_ty(*ty)?;
                BaseTyKind::Slice(Box::new(ty))
            }
        };
        Ok(BaseTy { kind, span: bty.span })
    }

    fn resolve_generic_arg(
        &self,
        arg: surface::GenericArg,
    ) -> Result<surface::GenericArg<Res>, ErrorGuaranteed> {
        match arg {
            surface::GenericArg::Type(ty) => Ok(surface::GenericArg::Type(self.resolve_ty(ty)?)),
            surface::GenericArg::Constraint(ident, ty) => {
                Ok(surface::GenericArg::Constraint(ident, self.resolve_ty(ty)?))
            }
        }
    }

    fn resolve_path(&self, path: Path) -> Result<Path<Res>, ErrorGuaranteed> {
        let Some(res) = self.table.get(&ResKey::from_path(&path)) else {
            return Err(self.sess.emit_err(errors::UnresolvedPath::new(&path)))
        };
        match res {
            &ResEntry::Res(res) => {
                let generics = path
                    .generics
                    .into_iter()
                    .map(|arg| self.resolve_generic_arg(arg))
                    .try_collect_exhaust()?;
                Ok(Path {
                    segments: path.segments,
                    generics,
                    refine: path.refine,
                    span: path.span,
                    res,
                })
            }
            ResEntry::Unsupported { reason, span } => {
                return Err(self
                    .sess
                    .emit_err(errors::UnsupportedSignature::new(*span, reason)))
            }
        }
    }
}

impl<'sess> NameResTable<'sess> {
    fn from_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let item = tcx.hir().expect_item(def_id);
        let mut table = Self::new(sess);
        match &item.kind {
            ItemKind::TyAlias(ty, _) => {
                table.collect_from_ty(ty)?;
            }
            ItemKind::Struct(data, _) => {
                table.insert(ResKey::from_ident(item.ident), Res::Struct(def_id.to_def_id()));

                for field in data.fields() {
                    table.collect_from_ty(field.ty)?;
                }
            }
            ItemKind::Enum(data, _) => {
                table.insert(ResKey::from_ident(item.ident), Res::Enum(def_id.to_def_id()));

                for variant in data.variants {
                    for field in variant.data.fields() {
                        table.collect_from_ty(field.ty)?;
                    }
                }
            }
            ItemKind::Fn(fn_sig, generics, ..) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_generics(generics)?;
            }
            _ => {}
        }
        Ok(table)
    }

    fn insert(&mut self, key: ResKey, res: impl Into<ResEntry>) {
        self.res.insert(key, res.into());
    }

    fn from_impl_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        def_id: LocalDefId,
    ) -> Result<Self, ErrorGuaranteed> {
        let impl_item = tcx.hir().expect_impl_item(def_id);

        let mut table = Self::new(sess);

        // Insert generics from parent impl
        if let Some(parent_impl_did) = tcx.impl_of_method(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());
            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                table.collect_from_ty(parent.self_ty)?;
            }
        }

        match &impl_item.kind {
            rustc_hir::ImplItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
            }
            rustc_hir::ImplItemKind::Const(_, _) | rustc_hir::ImplItemKind::Type(_) => {}
        }

        Ok(table)
    }

    fn new(sess: &'sess FluxSession) -> NameResTable<'sess> {
        NameResTable { sess, res: FxHashMap::default() }
    }

    fn get(&self, key: &ResKey) -> Option<&ResEntry> {
        self.res.get(key)
    }

    fn collect_from_generics(
        &mut self,
        generics: &hir::Generics<'_>,
    ) -> Result<(), ErrorGuaranteed> {
        // generics
        //     .params
        //     .iter()
        //     .try_for_each_exhaust(|param| self.collect_from_generic_param(param));

        generics
            .predicates
            .iter()
            .try_for_each_exhaust(|pred| self.collect_from_where_predicate(pred))
    }

    fn collect_from_where_predicate(
        &mut self,
        clause: &hir::WherePredicate,
    ) -> Result<(), ErrorGuaranteed> {
        if let hir::WherePredicate::BoundPredicate(bound) = clause {
            self.collect_from_ty(&bound.bounded_ty)?;
            bound
                .bounds
                .iter()
                .try_for_each_exhaust(|b| self.collect_from_generic_bound(b))?;
        }
        Ok(())
    }

    fn collect_from_generic_bound(
        &mut self,
        bound: &hir::GenericBound,
    ) -> Result<(), ErrorGuaranteed> {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref, _) => {
                self.collect_from_path(poly_trait_ref.trait_ref.path)
            }
            _ => Ok(()),
        }
    }

    fn collect_from_fn_sig(&mut self, fn_sig: &hir::FnSig) -> Result<(), ErrorGuaranteed> {
        fn_sig
            .decl
            .inputs
            .iter()
            .try_for_each_exhaust(|ty| self.collect_from_ty(ty))?;

        if let hir::FnRetTy::Return(ty) = fn_sig.decl.output {
            self.collect_from_ty(ty)?;
        }
        Ok(())
    }

    fn res_from_hir_res(&self, res: hir::def::Res, span: Span) -> ResEntry {
        match res {
            hir::def::Res::Def(hir::def::DefKind::TyParam, did) => ResEntry::Res(Res::Param(did)),
            hir::def::Res::Def(hir::def::DefKind::Struct, did) => ResEntry::Res(Res::Struct(did)),
            hir::def::Res::Def(hir::def::DefKind::Enum, did) => ResEntry::Res(Res::Enum(did)),
            hir::def::Res::PrimTy(prim_ty) => ResEntry::Res(Res::PrimTy(prim_ty)),
            hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id) => {
                ResEntry::Res(Res::Alias(def_id))
            }
            hir::def::Res::Def(hir::def::DefKind::Trait, def_id) => {
                ResEntry::Res(Res::Trait(def_id))
            }
            _ => {
                ResEntry::Unsupported { span, reason: format!("unsupported resolution `{res:?}`") }
            }
        }
    }

    fn collect_from_ty(&mut self, ty: &hir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => {
                self.collect_from_ty(mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(ty)),
            hir::TyKind::Path(qpath) => {
                let hir::QPath::Resolved(None, path) = qpath else {
            return Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                qpath.span(),
                "unsupported type",
            )));
        };
                self.collect_from_path(path)
            }
            hir::TyKind::BareFn(_)
            | hir::TyKind::Never
            | hir::TyKind::OpaqueDef(..)
            | hir::TyKind::TraitObject(..)
            | hir::TyKind::Typeof(_)
            | hir::TyKind::Infer
            | hir::TyKind::Err(_) => Ok(()),
        }
    }

    fn collect_from_path(&mut self, path: &hir::Path<'_>) -> Result<(), ErrorGuaranteed> {
        let key = ResKey::from_hir_path(self.sess, path)?;
        let res = self.res_from_hir_res(path.res, path.span);
        self.insert(key, res);

        if let [.., PathSegment { args, .. }] = path.segments {
            args.map(|args| args.args)
                .iter()
                .copied()
                .flatten()
                .try_for_each_exhaust(|arg| self.collect_from_generic_arg(arg))?;

            args.map(|args| args.bindings)
                .iter()
                .copied()
                .flatten()
                .try_for_each_exhaust(|binding| self.collect_from_type_binding(&binding))?;
        }
        Ok(())
    }

    fn collect_from_type_binding(
        &mut self,
        binding: &hir::TypeBinding<'_>,
    ) -> Result<(), ErrorGuaranteed> {
        match binding.kind {
            hir::TypeBindingKind::Equality { term } => self.collect_from_term(&term),
            hir::TypeBindingKind::Constraint { bounds } => {
                bounds
                    .iter()
                    .try_for_each_exhaust(|bound| self.collect_from_generic_bound(bound))
            }
        }
    }

    fn collect_from_term(&mut self, term: &hir::Term<'_>) -> Result<(), ErrorGuaranteed> {
        match term {
            hir::Term::Ty(ty) => self.collect_from_ty(ty),
            hir::Term::Const(_) => Ok(()),
        }
    }

    fn collect_from_generic_arg(&mut self, arg: &hir::GenericArg) -> Result<(), ErrorGuaranteed> {
        match arg {
            hir::GenericArg::Type(ty) => self.collect_from_ty(ty),
            hir::GenericArg::Lifetime(_) => Ok(()),
            hir::GenericArg::Const(_) => {
                Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                    arg.span(),
                    "const generics are not supported yet",
                )))
            }

            hir::GenericArg::Infer(_) => unreachable!(),
        }
    }
}

impl ResKey {
    fn from_ident(ident: Ident) -> Self {
        ResKey { s: format!("{ident}") }
    }

    fn from_path(path: &Path) -> ResKey {
        let s = path.segments.iter().join("::");
        ResKey { s }
    }

    fn from_hir_path(sess: &FluxSession, path: &rustc_hir::Path) -> Result<Self, ErrorGuaranteed> {
        if let [prefix @ .., _] = path.segments
           && prefix.iter().any(|segment| segment.args.is_some())
        {
            return Err(sess.emit_err(errors::UnsupportedSignature::new (
                path.span,
                "path segments with generic arguments are not supported",
            )));
        }
        let s = path.segments.iter().map(|segment| segment.ident).join("::");
        Ok(ResKey { s })
    }
}

impl From<Res> for ResEntry {
    fn from(res: Res) -> Self {
        ResEntry::Res(res)
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface;
    use itertools::Itertools;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(desugar_unsupported_signature, code = "FLUX")]
    #[note]
    pub(super) struct UnsupportedSignature<'a> {
        #[primary_span]
        span: Span,
        note: &'a str,
    }

    impl<'a> UnsupportedSignature<'a> {
        pub(super) fn new(span: Span, note: &'a str) -> Self {
            Self { span, note }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar_unresolved_path, code = "FLUX")]
    #[help]
    pub struct UnresolvedPath {
        #[primary_span]
        pub span: Span,
        pub path: String,
    }

    impl UnresolvedPath {
        pub fn new(path: &surface::Path) -> Self {
            Self { span: path.span, path: path.segments.iter().join("::") }
        }
    }
}
