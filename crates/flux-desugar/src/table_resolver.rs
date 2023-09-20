use flux_common::{bug, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::fhir::Res;
use flux_syntax::surface::{self, BaseTy, BaseTyKind, GenericBounds, Ident, Path, TraitRef, Ty};
use hir::{def::DefKind, ItemKind, OwnerId, PathSegment};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub struct Resolver<'genv> {
    sess: &'genv FluxSession,
    table: NameResTable<'genv>,
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct ResKey {
    s: String,
}

struct NameResTable<'sess> {
    res: UnordMap<ResKey, ResEntry>,
    opaque: Option<LocalDefId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
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
        let hir_id = tcx.hir().local_def_id_to_hir_id(def_id);
        let node = tcx.hir().get(hir_id);
        let table = match node {
            hir::Node::Item(item) => NameResTable::from_item(tcx, sess, item)?,
            hir::Node::ImplItem(impl_item) => NameResTable::from_impl_item(tcx, sess, impl_item)?,
            hir::Node::TraitItem(trait_item) => {
                NameResTable::from_trait_item(tcx, sess, trait_item)?
            }
            _ => {
                bug!("unsupported node {node:?}")
            }
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

    fn resolve_where_bound_predicate(
        &self,
        pred: surface::WhereBoundPredicate,
    ) -> Result<surface::WhereBoundPredicate<Res>, ErrorGuaranteed> {
        let bounded_ty = self.resolve_ty(pred.bounded_ty)?;
        let bounds = self.resolve_bounds(pred.bounds)?;
        Ok(surface::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
    }

    fn resolve_bounds(
        &self,
        bounds: surface::GenericBounds,
    ) -> Result<GenericBounds<Res>, ErrorGuaranteed> {
        let bounds = bounds
            .into_iter()
            .map(|bound| self.resolve_trait_ref(bound))
            .try_collect_exhaust()?;
        Ok(bounds)
    }

    fn resolve_trait_ref(
        &self,
        trait_ref: surface::TraitRef,
    ) -> Result<TraitRef<Res>, ErrorGuaranteed> {
        Ok(TraitRef { path: self.resolve_path(trait_ref.path)? })
    }

    fn resolve_constraint(
        &self,
        cstr: surface::Constraint,
    ) -> Result<surface::Constraint<Res>, ErrorGuaranteed> {
        match cstr {
            surface::Constraint::Type(ident, ty) => {
                Ok(surface::Constraint::Type(ident, self.resolve_ty(ty)?))
            }
            surface::Constraint::Pred(e) => Ok(surface::Constraint::Pred(e)),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn resolve_fn_sig(
        &self,
        fn_sig: surface::FnSig,
    ) -> Result<surface::FnSig<Res>, ErrorGuaranteed> {
        let asyncness = self.resolve_asyncness(fn_sig.asyncness);

        let args = fn_sig
            .args
            .into_iter()
            .map(|arg| self.resolve_arg(arg))
            .try_collect_exhaust();

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|cstr| self.resolve_constraint(cstr))
            .try_collect_exhaust()?;

        let predicates = fn_sig
            .predicates
            .into_iter()
            .map(|pred| {
                let pred = self.resolve_where_bound_predicate(pred)?;
                Ok(pred)
            })
            .try_collect_exhaust();

        let returns = self.resolve_fn_ret_ty(fn_sig.returns);

        Ok(surface::FnSig {
            asyncness: asyncness?,
            generics: fn_sig.generics,
            requires: fn_sig.requires,
            args: args?,
            returns: returns?,
            ensures,
            predicates: predicates?,
            span: fn_sig.span,
        })
    }

    fn resolve_asyncness(
        &self,
        asyncness: surface::Async,
    ) -> Result<surface::Async<Res>, ErrorGuaranteed> {
        match asyncness {
            surface::Async::Yes { span, .. } => {
                let res = self.resolve_opaque_impl(span)?;
                Ok(surface::Async::Yes { res, span })
            }
            surface::Async::No => Ok(surface::Async::No),
        }
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

    fn resolve_fn_ret_ty(
        &self,
        returns: surface::FnRetTy,
    ) -> Result<surface::FnRetTy<Res>, ErrorGuaranteed> {
        match returns {
            surface::FnRetTy::Default(span) => Ok(surface::FnRetTy::Default(span)),
            surface::FnRetTy::Ty(ty) => Ok(surface::FnRetTy::Ty(self.resolve_ty(ty)?)),
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
            surface::TyKind::ImplTrait(_, bounds) => {
                let bounds = self.resolve_bounds(bounds)?;
                let res = self.resolve_opaque_impl(ty.span)?;
                surface::TyKind::ImplTrait(res, bounds)
            },
        };
        Ok(surface::Ty { kind, span: ty.span })
    }

    fn resolve_opaque_impl(&self, span: Span) -> Result<Res, ErrorGuaranteed> {
        if let Some(def_id) = self.table.opaque {
            Ok(Res::Def(DefKind::OpaqueTy, def_id.to_def_id()))
        } else {
            Err(self
                .sess
                .emit_err(errors::UnresolvedPath { span, path: "opaque type".into() }))
        }
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
            return Err(self.sess.emit_err(errors::UnresolvedPath::new(&path)));
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
    fn new(sess: &'sess FluxSession) -> NameResTable<'sess> {
        NameResTable { sess, opaque: None, res: UnordMap::default() }
    }

    fn from_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        item: &hir::Item,
    ) -> Result<Self, ErrorGuaranteed> {
        let mut table = Self::new(sess);
        let def_id = item.owner_id.def_id;
        match &item.kind {
            ItemKind::TyAlias(ty, _) => {
                table.collect_from_ty(ty)?;
            }
            ItemKind::Struct(data, _) => {
                table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Struct, def_id.to_def_id()),
                );

                for field in data.fields() {
                    table.collect_from_ty(field.ty)?;
                }
            }
            ItemKind::Enum(data, _) => {
                table.insert(
                    ResKey::from_ident(item.ident),
                    Res::Def(DefKind::Enum, def_id.to_def_id()),
                );

                for variant in data.variants {
                    for field in variant.data.fields() {
                        table.collect_from_ty(field.ty)?;
                    }
                }
            }
            ItemKind::Fn(fn_sig, generics, ..) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_generics(generics)?;
                table.collect_from_opaque_impls(tcx)?;
            }
            _ => {}
        }
        Ok(table)
    }

    fn from_impl_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        impl_item: &hir::ImplItem,
    ) -> Result<Self, ErrorGuaranteed> {
        let def_id = impl_item.owner_id.def_id;

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
                table.collect_from_opaque_impls(tcx)?;
            }
            rustc_hir::ImplItemKind::Const(_, _) | rustc_hir::ImplItemKind::Type(_) => {}
        }

        Ok(table)
    }

    fn from_trait_item(
        tcx: TyCtxt,
        sess: &'sess FluxSession,
        trait_item: &hir::TraitItem,
    ) -> Result<Self, ErrorGuaranteed> {
        let def_id = trait_item.owner_id.def_id;

        let mut table = Self::new(sess);

        // Insert generics from parent trait
        if let Some(parent_impl_did) = tcx.trait_of_item(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());
            if let ItemKind::Impl(parent) = &parent_impl_item.kind {
                table.collect_from_ty(parent.self_ty)?;
            }
        }

        match &trait_item.kind {
            rustc_hir::TraitItemKind::Fn(fn_sig, _) => {
                table.collect_from_fn_sig(fn_sig)?;
                table.collect_from_opaque_impls(tcx)?;
            }
            rustc_hir::TraitItemKind::Const(..) | rustc_hir::TraitItemKind::Type(..) => {}
        }

        Ok(table)
    }

    fn insert(&mut self, key: ResKey, res: impl Into<ResEntry>) {
        self.res.insert(key, res.into());
    }

    fn get(&self, key: &ResKey) -> Option<&ResEntry> {
        self.res.get(key)
    }

    fn collect_from_generics(
        &mut self,
        generics: &hir::Generics<'_>,
    ) -> Result<(), ErrorGuaranteed> {
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
            self.collect_from_ty(bound.bounded_ty)?;
            self.collect_from_generic_bounds(bound.bounds)?;
        }
        Ok(())
    }

    fn collect_from_generic_bounds(
        &mut self,
        bounds: &[hir::GenericBound<'_>],
    ) -> Result<(), ErrorGuaranteed> {
        bounds
            .iter()
            .try_for_each_exhaust(|b| self.collect_from_generic_bound(b))?;
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
            hir::GenericBound::LangItemTrait(_lang_item, _span, _hir_id, args) => {
                self.collect_from_generic_args(args)
            }
            _ => Ok(()),
        }
    }

    fn collect_from_opaque_impls(&mut self, tcx: TyCtxt) -> Result<(), ErrorGuaranteed> {
        if let Some(did) = self.opaque {
            let owner_id = OwnerId { def_id: did };
            let item_id = hir::ItemId { owner_id };
            let item_kind = tcx.hir().item(item_id).kind;
            if let ItemKind::OpaqueTy(opaque_ty) = item_kind {
                self.collect_from_generic_bounds(opaque_ty.bounds)?;
            }
        }
        Ok(())
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
            hir::TyKind::OpaqueDef(item_id, ..) => {
                assert!(self.opaque.is_none());
                if self.opaque.is_some() {
                    Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                        ty.span,
                        "duplicate opaque types in signature",
                    )))
                } else {
                    self.opaque = Some(item_id.owner_id.def_id);
                    Ok(())
                }
            }
            hir::TyKind::BareFn(_)
            | hir::TyKind::Never
            | hir::TyKind::TraitObject(..)
            | hir::TyKind::Typeof(_)
            | hir::TyKind::Infer
            | hir::TyKind::Err(_) => Ok(()),
        }
    }

    fn collect_from_generic_args(
        &mut self,
        args: &rustc_hir::GenericArgs,
    ) -> Result<(), ErrorGuaranteed> {
        args.args
            .iter()
            .copied()
            .try_for_each_exhaust(|arg| self.collect_from_generic_arg(&arg))?;

        args.bindings
            .iter()
            .copied()
            .try_for_each_exhaust(|binding| self.collect_from_type_binding(&binding))?;
        Ok(())
    }

    fn collect_from_path(&mut self, path: &hir::Path<'_>) -> Result<(), ErrorGuaranteed> {
        let key = ResKey::from_hir_path(self.sess, path)?;

        let res = path
            .res
            .try_into()
            .map_or_else(|_| ResEntry::unsupported(*path), ResEntry::Res);
        self.insert(key, res);

        if let [.., PathSegment { args: Some(args), .. }] = path.segments {
            self.collect_from_generic_args(args)?;
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

impl ResEntry {
    fn unsupported(path: hir::Path) -> Self {
        Self::Unsupported { span: path.span, reason: format!("unsupported res `{:?}`", path.res) }
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
