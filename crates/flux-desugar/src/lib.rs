//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]

#![feature(rustc_private, min_specialization, box_patterns, never_type, unwrap_infallible)]

extern crate rustc_data_structures;
extern crate rustc_errors;

extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::RustItemCtxt;
use flux_common::result::{ErrorCollector, ResultExt};
use flux_macros::fluent_messages;
use rustc_data_structures::unord::UnordMap;

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;

use flux_middle::{
    ResolverOutput, Specs,
    def_id::FluxLocalDefId,
    fhir,
    global_env::GlobalEnv,
    queries::{Providers, QueryErr, QueryResult},
    query_bug,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{self as hir, OwnerId};
use rustc_span::def_id::LocalDefId;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub fn provide(providers: &mut Providers) {
    providers.resolve_crate = resolver::resolve_crate;
    providers.desugar = desugar;
    providers.fhir_crate = desugar_crate;
}

pub fn desugar<'genv>(
    genv: GlobalEnv<'genv, '_>,
    def_id: LocalDefId,
) -> QueryResult<UnordMap<LocalDefId, fhir::Node<'genv>>> {
    if genv.ignored(def_id) {
        return Err(QueryErr::Ignored { def_id: def_id.to_def_id() });
    }

    let cx = DesugarCtxt { genv, resolver_output: genv.resolve_crate() };
    let specs = genv.collect_specs();
    let owner_id = OwnerId { def_id };
    let mut nodes = UnordMap::default();

    match genv.tcx().hir_node_by_def_id(def_id) {
        rustc_hir::Node::Item(item) => {
            match item.kind {
                hir::ItemKind::Fn { .. } => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                        cx.desugar_item_fn(fn_spec)
                    })?;
                    nodes.extend(opaque_tys.into_iter().map(|opaque_ty| {
                        (opaque_ty.def_id.local_id(), fhir::Node::OpaqueTy(opaque_ty))
                    }));
                    nodes.insert(def_id, fhir::Node::Item(genv.alloc(item)));
                }
                hir::ItemKind::TyAlias(..) => {
                    let ty_alias = specs.ty_aliases[&owner_id].as_ref();
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_type_alias(ty_alias)),
                        )?)),
                    );
                }

                hir::ItemKind::Enum(..) => {
                    let enum_def = &specs.enums[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| cx.desugar_enum_def(enum_def),
                        )?)),
                    );
                }
                hir::ItemKind::Union(..) => {
                    let union_def = &specs.structs[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_struct_def(union_def)),
                        )?)),
                    );
                }
                hir::ItemKind::Struct(..) => {
                    let struct_def = &specs.structs[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_struct_def(struct_def)),
                        )?)),
                    );
                }
                hir::ItemKind::Trait(..) => {
                    let trait_ = &specs.traits[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| cx.desugar_trait(trait_),
                        )?)),
                    );
                }
                hir::ItemKind::Impl(..) => {
                    let impl_ = &specs.impls[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_impl(impl_)),
                        )?)),
                    );
                }
                hir::ItemKind::Const(..) => {
                    let constant_ = match specs.constants.get(&owner_id) {
                        Some(constant_) => constant_,
                        None => &surface::ConstantInfo { expr: None },
                    };

                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_const(constant_)),
                        )?)),
                    );
                }
                _ => Err(query_bug!(def_id, "unsupported item"))?,
            }
        }
        rustc_hir::Node::TraitItem(trait_item) => {
            match trait_item.kind {
                rustc_hir::TraitItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                        cx.desugar_trait_fn(fn_spec)
                    })?;
                    nodes.extend(opaque_tys.into_iter().map(|opaque_ty| {
                        (opaque_ty.def_id.local_id(), fhir::Node::OpaqueTy(opaque_ty))
                    }));
                    nodes.insert(def_id, fhir::Node::TraitItem(genv.alloc(item)));
                }
                rustc_hir::TraitItemKind::Type(..) => {
                    let item = cx.with_rust_item_ctxt(owner_id, None, |cx| {
                        Ok(cx.desugar_trait_assoc_ty())
                    })?;
                    nodes.insert(owner_id.def_id, fhir::Node::TraitItem(genv.alloc(item)));
                }
                rustc_hir::TraitItemKind::Const(..) => {
                    nodes.insert(
                        def_id,
                        fhir::Node::TraitItem(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_trait_const()),
                        )?)),
                    );
                }
            }
        }
        rustc_hir::Node::ImplItem(impl_item) => {
            match &impl_item.kind {
                rustc_hir::ImplItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                        cx.desugar_impl_fn(fn_spec)
                    })?;
                    nodes.extend(opaque_tys.into_iter().map(|opaque_ty| {
                        (opaque_ty.def_id.local_id(), fhir::Node::OpaqueTy(opaque_ty))
                    }));
                    nodes.insert(def_id, fhir::Node::ImplItem(genv.alloc(item)));
                }
                rustc_hir::ImplItemKind::Type(..) => {
                    let item = cx
                        .with_rust_item_ctxt(owner_id, None, |cx| Ok(cx.desugar_impl_assoc_ty()))?;
                    nodes.insert(owner_id.def_id, fhir::Node::ImplItem(genv.alloc(item)));
                }
                rustc_hir::ImplItemKind::Const(..) => {
                    nodes.insert(
                        def_id,
                        fhir::Node::ImplItem(genv.alloc(cx.with_rust_item_ctxt(
                            owner_id,
                            None,
                            |cx| Ok(cx.desugar_impl_const()),
                        )?)),
                    );
                }
            }
        }
        rustc_hir::Node::AnonConst(..) => {
            nodes.insert(def_id, fhir::Node::AnonConst);
        }
        rustc_hir::Node::Expr(..) => {
            nodes.insert(def_id, fhir::Node::Expr);
        }
        rustc_hir::Node::ForeignItem(foreign) => {
            let foreign_item = fhir::Node::ForeignItem(genv.alloc(cx.with_rust_item_ctxt(
                owner_id,
                None,
                |cx| cx.desugar_foreign_item(*foreign),
            )?));
            nodes.insert(def_id, foreign_item);
        }
        rustc_hir::Node::Ctor(rustc_hir::VariantData::Tuple(_, _, _)) => {
            nodes.insert(def_id, fhir::Node::Ctor);
        }
        node => {
            if let Some(ident) = node.ident() {
                Err(query_bug!(def_id, "unsupported item {ident:?}"))?;
            } else {
                Err(query_bug!(def_id, "unsupported item"))?;
            }
        }
    }
    Ok(nodes)
}

struct DesugarCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    resolver_output: &'genv ResolverOutput,
}

impl<'genv, 'tcx> DesugarCtxt<'genv, 'tcx> {
    fn with_rust_item_ctxt<'a, T>(
        &'a self,
        owner_id: OwnerId,
        opaque_tys: Option<&'a mut Vec<&'genv fhir::OpaqueTy<'genv>>>,
        f: impl FnOnce(&mut RustItemCtxt<'a, 'genv, 'tcx>) -> Result<T>,
    ) -> Result<T> {
        let owner_id = self
            .genv
            .maybe_extern_id(owner_id.def_id)
            .map(|def_id| OwnerId { def_id });
        RustItemCtxt::with(self.genv, owner_id, self.resolver_output, opaque_tys, f)
    }
}

fn desugar_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> fhir::FluxItems<'genv> {
    match try_desugar_crate(genv) {
        Ok(fhir) => fhir,
        Err(err) => {
            // There's too much code down the pipeline that relies on having the fhir, so we abort
            // if there are any error during desugaring to avoid propagating the error back the query
            // system. We should probably move away from desugaring the entire crate in one go and
            // instead desugar items on demand so we can fail on a per item basis.
            genv.sess().abort(err);
        }
    }
}

fn try_desugar_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> Result<fhir::FluxItems<'genv>> {
    let specs = genv.collect_specs();
    let fhir = fhir::FluxItems::new();
    let resolver_output = genv.resolve_crate();
    let mut cx = CrateDesugar::new(genv, fhir, resolver_output);
    cx.desugar_flux_items(specs);

    cx.err.into_result()?;
    Ok(cx.fhir)
}

struct CrateDesugar<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    fhir: fhir::FluxItems<'genv>,
    resolver_output: &'genv ResolverOutput,
    err: Option<ErrorGuaranteed>,
}

impl<'genv, 'tcx> CrateDesugar<'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        fhir: fhir::FluxItems<'genv>,
        resolver_output: &'genv ResolverOutput,
    ) -> Self {
        Self { genv, fhir, resolver_output, err: None }
    }
}

impl CrateDesugar<'_, '_> {
    #[allow(clippy::disallowed_methods, reason = "`flux_items_by_parent` is the source of truth")]
    fn desugar_flux_items(&mut self, specs: &Specs) {
        for (parent, items) in &specs.flux_items_by_parent {
            for item in items {
                let def_id = FluxLocalDefId::new(parent.def_id, item.name().name);
                match item {
                    surface::Item::Qualifier(qual) => {
                        self.desugar_qualifier(def_id, qual)
                            .collect_err(&mut self.err);
                    }
                    surface::Item::FuncDef(defn) => {
                        self.desugar_func_defn(def_id, defn)
                            .collect_err(&mut self.err);
                    }
                    surface::Item::SortDecl(_) => {}
                    surface::Item::PrimProp(prim_prop) => {
                        self.desugar_prim_prop(def_id, prim_prop)
                            .collect_err(&mut self.err);
                    }
                }
            }
        }
    }

    fn desugar_prim_prop(&mut self, def_id: FluxLocalDefId, prop: &surface::PrimOpProp) -> Result {
        let prop = desugar::desugar_prim_prop(self.genv, self.resolver_output, def_id, prop)?;
        self.fhir
            .items
            .insert(def_id, fhir::FluxItem::PrimProp(self.genv.alloc(prop)));
        Ok(())
    }

    fn desugar_func_defn(&mut self, def_id: FluxLocalDefId, func: &surface::SpecFunc) -> Result {
        let func = desugar::desugar_spec_func(self.genv, self.resolver_output, def_id, func)?;
        self.fhir
            .items
            .insert(def_id, fhir::FluxItem::Func(self.genv.alloc(func)));
        Ok(())
    }

    fn desugar_qualifier(
        &mut self,
        def_id: FluxLocalDefId,
        qualifier: &surface::Qualifier,
    ) -> Result {
        let qualifier =
            desugar::desugar_qualifier(self.genv, self.resolver_output, def_id, qualifier)?;
        self.fhir
            .items
            .insert(def_id, fhir::FluxItem::Qualifier(self.genv.alloc(qualifier)));
        Ok(())
    }
}
