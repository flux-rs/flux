use std::collections::hash_map;

use flux_common::{bug, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, Res},
    Specs,
};
use flux_syntax::surface::{self, AliasPred, BaseTy, BaseTyKind, Ident, Path, Pred, PredKind, Ty};
use hir::{def::DefKind, ItemId, ItemKind, OwnerId, PathSegment};
use itertools::Itertools;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::ErrorGuaranteed;
use rustc_hir as hir;
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, Span, Symbol};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn resolve_crate(
    tcx: TyCtxt,
    sess: &FluxSession,
    specs: &Specs,
) -> Result<ResolverOutput> {
    let mut resolver = Resolver::new(tcx, sess);
    tcx.hir_crate_items(())
        .owners()
        .try_for_each_exhaust(|id| {
            match tcx.def_kind(id) {
                DefKind::Struct => resolver.resolve_struct_def(id, &specs.structs[&id])?,
                DefKind::Enum => resolver.resolve_enum_def(id, &specs.enums[&id])?,
                DefKind::TyAlias { .. } => {
                    if let Some(type_alias) = &specs.ty_aliases[&id] {
                        resolver.resolve_type_alias(id, type_alias)?;
                    }
                }
                DefKind::Fn | DefKind::AssocFn => {
                    if let Some(fn_sig) = specs.fn_sigs[&id].fn_sig.as_ref() {
                        resolver.resolve_fn_sig(id, fn_sig)?;
                    }
                }
                _ => {}
            }
            Ok(())
        })?;
    let mut resolver_output = resolver.into_output();

    collect_flux_global_items(tcx, &mut resolver_output, specs);

    Ok(resolver_output)
}

struct Resolver<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    output: ResolverOutput,
}

#[derive(Default)]
pub(crate) struct ResolverOutput {
    pub path_res_map: UnordMap<surface::NodeId, Res>,
    pub impl_trait_res_map: UnordMap<surface::NodeId, ItemId>,
    pub func_decls: UnordMap<Symbol, fhir::FuncKind>,
    pub sort_decls: UnordMap<Symbol, fhir::SortDecl>,
    pub consts: UnordMap<Symbol, DefId>,
}

fn collect_flux_global_items(tcx: TyCtxt, resolver_output: &mut ResolverOutput, specs: &Specs) {
    for sort_decl in &specs.sort_decls {
        resolver_output.sort_decls.insert(
            sort_decl.name.name,
            fhir::SortDecl { name: sort_decl.name.name, span: sort_decl.name.span },
        );
    }

    for def_id in specs.consts.keys() {
        let did = def_id.to_def_id();
        let sym = super::def_id_symbol(tcx, *def_id);
        resolver_output.consts.insert(sym, did);
    }

    for defn in &specs.func_defs {
        let kind = if defn.body.is_some() { fhir::FuncKind::Def } else { fhir::FuncKind::Uif };
        resolver_output.func_decls.insert(defn.name.name, kind);
    }

    for itf in flux_middle::theory_funcs() {
        resolver_output
            .func_decls
            .insert(itf.name, fhir::FuncKind::Thy(itf.fixpoint_name));
    }
}

impl<'a, 'tcx> Resolver<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession) -> Self {
        Self { tcx, sess, output: ResolverOutput::default() }
    }

    pub fn into_output(self) -> ResolverOutput {
        self.output
    }

    pub fn resolve_type_alias(
        &mut self,
        owner_id: OwnerId,
        alias_def: &surface::TyAlias,
    ) -> Result {
        ItemLikeResolver::new(self.tcx, self.sess, owner_id, &mut self.output)?
            .resolve_ty(&alias_def.ty)
    }

    pub fn resolve_struct_def(
        &mut self,
        owner_id: OwnerId,
        struct_def: &surface::StructDef,
    ) -> Result {
        if !struct_def.needs_resolving() {
            return Ok(());
        }

        let mut item_resolver =
            ItemLikeResolver::new(self.tcx, self.sess, owner_id, &mut self.output)?;
        struct_def.fields.iter().try_for_each_exhaust(|ty| {
            if let Some(ty) = ty {
                item_resolver.resolve_ty(ty)?;
            }
            Ok(())
        })
    }

    pub fn resolve_enum_def(&mut self, owner_id: OwnerId, enum_def: &surface::EnumDef) -> Result {
        if !enum_def.needs_resolving() {
            return Ok(());
        }

        let mut item_resolver =
            ItemLikeResolver::new(self.tcx, self.sess, owner_id, &mut self.output)?;
        enum_def
            .variants
            .iter()
            .try_for_each_exhaust(|variant| item_resolver.resolve_variant(variant.as_ref()))
    }

    pub fn resolve_fn_sig(&mut self, owner_id: OwnerId, fn_sig: &surface::FnSig) -> Result {
        let mut item_resolver =
            ItemLikeResolver::new(self.tcx, self.sess, owner_id, &mut self.output)?;
        let asyncness = item_resolver.resolve_asyncness(&fn_sig.asyncness);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|arg| item_resolver.resolve_arg(arg));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|cstr| item_resolver.resolve_constraint(cstr));

        let predicates = fn_sig
            .generics
            .predicates
            .iter()
            .try_for_each_exhaust(|pred| item_resolver.resolve_where_bound_predicate(pred));

        let returns = item_resolver.resolve_fn_ret_ty(&fn_sig.returns);

        asyncness?;
        args?;
        returns?;
        predicates?;
        ensures?;

        Ok(())
    }
}

struct ItemLikeResolver<'a> {
    sess: &'a FluxSession,
    table: NameResTable<'a>,
    output: &'a mut ResolverOutput,
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct ResKey {
    s: String,
}

struct NameResTable<'sess> {
    res: UnordMap<ResKey, ResEntry>,
    opaque: Option<ItemId>, // TODO: HACK! need to generalize to multiple opaque types/impls in a signature.
    sess: &'sess FluxSession,
}

#[derive(Debug, PartialEq, Eq)]
enum ResEntry {
    Res(Res),
    Unsupported { reason: String, span: Span },
}

impl<'a> ItemLikeResolver<'a> {
    fn new(
        tcx: TyCtxt,
        sess: &'a FluxSession,
        owner_id: OwnerId,
        output: &'a mut ResolverOutput,
    ) -> Result<Self> {
        let table = match tcx.hir().owner(owner_id) {
            hir::OwnerNode::Item(item) => NameResTable::from_item(tcx, sess, item)?,
            hir::OwnerNode::ImplItem(impl_item) => {
                NameResTable::from_impl_item(tcx, sess, impl_item)?
            }
            hir::OwnerNode::TraitItem(trait_item) => {
                NameResTable::from_trait_item(tcx, sess, trait_item)?
            }
            node @ (hir::OwnerNode::ForeignItem(_) | hir::OwnerNode::Crate(_)) => {
                bug!("unsupported node {node:?}")
            }
        };

        Ok(Self { sess, table, output })
    }

    fn resolve_variant(&mut self, variant_def: Option<&surface::VariantDef>) -> Result {
        if let Some(variant_def) = variant_def {
            variant_def
                .fields
                .iter()
                .try_for_each_exhaust(|ty| self.resolve_ty(ty))?;
            if let Some(ret) = &variant_def.ret {
                self.resolve_variant_ret(ret)?;
            }
        }
        Ok(())
    }

    fn resolve_variant_ret(&mut self, ret: &surface::VariantRet) -> Result {
        self.resolve_path(&ret.path)
    }

    fn resolve_where_bound_predicate(&mut self, pred: &surface::WhereBoundPredicate) -> Result {
        self.resolve_ty(&pred.bounded_ty)?;
        self.resolve_bounds(&pred.bounds)
    }

    fn resolve_bounds(&mut self, bounds: &surface::GenericBounds) -> Result {
        bounds
            .iter()
            .try_for_each_exhaust(|trait_ref| self.resolve_trait_ref(trait_ref))
    }

    fn resolve_trait_ref(&mut self, trait_ref: &surface::TraitRef) -> Result {
        self.resolve_path(&trait_ref.path)
    }

    fn resolve_constraint(&mut self, cstr: &surface::Constraint) -> Result {
        match cstr {
            surface::Constraint::Type(_, ty) => self.resolve_ty(ty),
            surface::Constraint::Pred(_) => Ok(()),
        }
    }

    fn resolve_asyncness(&mut self, asyncness: &surface::Async) -> Result {
        match asyncness {
            surface::Async::Yes { node_id, span } => self.resolve_opaque_impl(*node_id, *span),
            surface::Async::No => Ok(()),
        }
    }

    fn resolve_arg(&mut self, arg: &surface::Arg) -> Result {
        match arg {
            surface::Arg::Constr(_, path, _) => self.resolve_path(path),
            surface::Arg::StrgRef(_, ty) => self.resolve_ty(ty),
            surface::Arg::Ty(_, ty) => self.resolve_ty(ty),
        }
    }

    fn resolve_fn_ret_ty(&mut self, returns: &surface::FnRetTy) -> Result {
        match returns {
            surface::FnRetTy::Default(_) => Ok(()),
            surface::FnRetTy::Ty(ty) => self.resolve_ty(ty),
        }
    }

    fn resolve_alias_pred(&mut self, alias_pred: &AliasPred) -> Result {
        self.resolve_path(&alias_pred.trait_id)?;
        alias_pred
            .generic_args
            .iter()
            .try_for_each_exhaust(|arg| self.resolve_generic_arg(arg))
    }

    fn resolve_pred(&mut self, pred: &Pred) -> Result {
        match &pred.kind {
            PredKind::Expr(_) => Ok(()),
            PredKind::Alias(alias_pred, _) => self.resolve_alias_pred(alias_pred),
        }
    }

    fn resolve_ty(&mut self, ty: &Ty) -> Result {
        match &ty.kind {
            surface::TyKind::Base(bty) => {
                // CODESYNC(type-holes, 3) we don't resolve type holes because they will be desugared
                // to `fhir::TyKind::Hole`. The path won't have an entry in `path_res_map` which we
                // should consider during desugaring. Holes in other positions (e.g., _[10] or _{v: v > 0})
                // will fail resolving so they don't show up in desugaring.
                if let BaseTyKind::Path(path) = &bty.kind
                    && path.is_hole()
                {
                    Ok(())
                } else {
                    self.resolve_bty(bty)
                }
            }
            surface::TyKind::Indexed { bty, .. } => self.resolve_bty(bty),
            surface::TyKind::Exists { bty, pred, .. } => {
                self.resolve_bty(bty)?;
                self.resolve_pred(pred)
            }
            surface::TyKind::GeneralExists { ty, .. } => self.resolve_ty(ty),
            surface::TyKind::Ref(_, ty) => self.resolve_ty(ty),
            surface::TyKind::Constr(pred, ty) => {
                self.resolve_pred(pred)?;
                self.resolve_ty(ty)
            }
            surface::TyKind::Tuple(tys) => {
                tys.iter().try_for_each_exhaust(|ty| self.resolve_ty(ty))
            }
            surface::TyKind::Array(ty, _) => self.resolve_ty(ty),
            surface::TyKind::ImplTrait(node_id, bounds) => {
                self.resolve_bounds(bounds)?;
                self.resolve_opaque_impl(*node_id, ty.span)
            }
        }
    }

    fn resolve_opaque_impl(&mut self, node_id: surface::NodeId, span: Span) -> Result {
        if let Some(def_id) = self.table.opaque {
            self.output.impl_trait_res_map.insert(node_id, def_id);
            Ok(())
        } else {
            Err(self
                .sess
                .emit_err(errors::UnresolvedPath { span, path: "opaque type".into() }))
        }
    }

    fn resolve_bty(&mut self, bty: &BaseTy) -> Result {
        match &bty.kind {
            BaseTyKind::Path(path) => self.resolve_path(path),
            BaseTyKind::Slice(ty) => self.resolve_ty(ty),
        }
    }

    fn resolve_generic_arg(&mut self, arg: &surface::GenericArg) -> Result {
        match arg {
            surface::GenericArg::Type(ty) => self.resolve_ty(ty),
            surface::GenericArg::Constraint(_, ty) => self.resolve_ty(ty),
        }
    }

    fn resolve_path(&mut self, path: &Path) -> Result {
        let Some(res) = self.table.get(&ResKey::from_path(path)) else {
            return Err(self.sess.emit_err(errors::UnresolvedPath::new(path)));
        };
        match res {
            &ResEntry::Res(res) => {
                self.output.path_res_map.insert(path.node_id, res);
                path.generics
                    .iter()
                    .try_for_each_exhaust(|arg| self.resolve_generic_arg(arg))
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

    fn from_item(tcx: TyCtxt, sess: &'sess FluxSession, item: &hir::Item) -> Result<Self> {
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
    ) -> Result<Self> {
        let def_id = impl_item.owner_id.def_id;

        let mut table = Self::new(sess);

        table.collect_from_generics(impl_item.generics)?;

        // Insert paths from parent impl
        let impl_did = tcx.local_parent(def_id);
        if let ItemKind::Impl(impl_) = &tcx.hir().expect_item(impl_did).kind {
            if let Some(trait_ref) = impl_.of_trait {
                let trait_id = trait_ref.trait_def_id().unwrap();
                table.insert(
                    ResKey::from_hir_path(sess, trait_ref.path)?,
                    Res::Def(DefKind::Trait, trait_id),
                );
            }
            table.collect_from_generics(impl_.generics)?;
            table.collect_from_ty(impl_.self_ty)?;
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
    ) -> Result<Self> {
        let def_id = trait_item.owner_id.def_id;

        let mut table = Self::new(sess);

        // Insert generics from parent trait
        if let Some(parent_impl_did) = tcx.trait_of_item(def_id.to_def_id()) {
            let parent_impl_item = tcx.hir().expect_item(parent_impl_did.expect_local());

            // Insert NAME of parent trait
            if let ItemKind::Trait(..) = &parent_impl_item.kind {
                table.insert(
                    ResKey::from_ident(parent_impl_item.ident),
                    Res::Def(DefKind::Trait, parent_impl_did),
                );
            }

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
        let res = res.into();
        match self.res.entry(key) {
            hash_map::Entry::Occupied(entry) => {
                if let ResEntry::Res(_) = res {
                    assert_eq!(entry.get(), &res);
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(res);
            }
        }
    }

    fn get(&self, key: &ResKey) -> Option<&ResEntry> {
        self.res.get(key)
    }

    fn collect_from_generics(&mut self, generics: &hir::Generics<'_>) -> Result {
        generics
            .predicates
            .iter()
            .try_for_each_exhaust(|pred| self.collect_from_where_predicate(pred))
    }

    fn collect_from_where_predicate(&mut self, clause: &hir::WherePredicate) -> Result {
        if let hir::WherePredicate::BoundPredicate(bound) = clause {
            self.collect_from_ty(bound.bounded_ty)?;
            self.collect_from_generic_bounds(bound.bounds)?;
        }
        Ok(())
    }

    fn collect_from_generic_bounds(&mut self, bounds: &[hir::GenericBound<'_>]) -> Result {
        bounds
            .iter()
            .try_for_each_exhaust(|b| self.collect_from_generic_bound(b))?;
        Ok(())
    }

    fn collect_from_generic_bound(&mut self, bound: &hir::GenericBound) -> Result {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref, _) => {
                self.collect_from_path(poly_trait_ref.trait_ref.path)
            }
            hir::GenericBound::LangItemTrait(.., args) => self.collect_from_generic_args(args),
            _ => Ok(()),
        }
    }

    fn collect_from_opaque_impls(&mut self, tcx: TyCtxt) -> Result {
        if let Some(item_id) = self.opaque {
            let item_kind = tcx.hir().item(item_id).kind;
            if let ItemKind::OpaqueTy(opaque_ty) = item_kind {
                self.collect_from_generic_bounds(opaque_ty.bounds)?;
            }
        }
        Ok(())
    }

    fn collect_from_fn_sig(&mut self, fn_sig: &hir::FnSig) -> Result {
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

    fn collect_from_ty(&mut self, ty: &hir::Ty) -> Result {
        match &ty.kind {
            hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => self.collect_from_ty(ty),
            hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => {
                self.collect_from_ty(mut_ty.ty)
            }
            hir::TyKind::Tup(tys) => tys.iter().try_for_each(|ty| self.collect_from_ty(ty)),
            hir::TyKind::Path(qpath) => {
                match qpath {
                    hir::QPath::Resolved(self_ty, path) => {
                        self.collect_from_path(path)?;
                        if let Some(self_ty) = self_ty {
                            self.collect_from_ty(self_ty)?;
                        }
                    }
                    hir::QPath::TypeRelative(ty, _path_segment) => {
                        self.collect_from_ty(ty)?;
                    }
                    hir::QPath::LangItem(..) => {}
                }
                Ok(())
            }
            hir::TyKind::OpaqueDef(item_id, ..) => {
                assert!(self.opaque.is_none());
                if self.opaque.is_some() {
                    Err(self.sess.emit_err(errors::UnsupportedSignature::new(
                        ty.span,
                        "duplicate opaque types in signature",
                    )))
                } else {
                    self.opaque = Some(*item_id);
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

    fn collect_from_generic_args(&mut self, args: &rustc_hir::GenericArgs) -> Result {
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

    fn collect_from_path(&mut self, path: &hir::Path<'_>) -> Result {
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

    fn collect_from_type_binding(&mut self, binding: &hir::TypeBinding<'_>) -> Result {
        match binding.kind {
            hir::TypeBindingKind::Equality { term } => self.collect_from_term(&term),
            hir::TypeBindingKind::Constraint { bounds } => {
                bounds
                    .iter()
                    .try_for_each_exhaust(|bound| self.collect_from_generic_bound(bound))
            }
        }
    }

    fn collect_from_term(&mut self, term: &hir::Term<'_>) -> Result {
        match term {
            hir::Term::Ty(ty) => self.collect_from_ty(ty),
            hir::Term::Const(_) => Ok(()),
        }
    }

    fn collect_from_generic_arg(&mut self, arg: &hir::GenericArg) -> Result {
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

    fn from_hir_path(sess: &FluxSession, path: &rustc_hir::Path) -> Result<Self> {
        if let [prefix @ .., _] = path.segments
            && prefix.iter().any(|segment| segment.args.is_some())
        {
            return Err(sess.emit_err(errors::UnsupportedSignature::new(
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
