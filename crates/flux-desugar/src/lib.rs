//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]

#![feature(rustc_private, min_specialization, box_patterns, let_chains, never_type)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::RustItemCtxt;
use flux_common::{bug, span_bug};
use flux_macros::fluent_messages;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;

use flux_middle::{
    fhir,
    global_env::GlobalEnv,
    queries::{Providers, QueryErr, QueryResult},
    ResolverOutput, Specs,
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
    match genv.tcx().hir_owner_node(owner_id) {
        rustc_hir::OwnerNode::Item(item) => {
            match item.kind {
                hir::ItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx
                        .as_rust_item_ctxt(owner_id, Some(&mut opaque_tys))
                        .desugar_item_fn(fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items().map(|(def_id, opaque_ty)| {
                        (def_id, fhir::Node::Item(genv.alloc(opaque_ty)))
                    }));
                    nodes.insert(def_id, fhir::Node::Item(genv.alloc(item)));
                }
                hir::ItemKind::TyAlias(..) => {
                    let ty_alias = specs.ty_aliases[&owner_id].as_ref();
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(
                            genv.alloc(
                                cx.as_rust_item_ctxt(owner_id, None)
                                    .desugar_type_alias(ty_alias)?,
                            ),
                        ),
                    );
                }

                hir::ItemKind::Enum(..) => {
                    let enum_def = &specs.enums[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(
                            genv.alloc(
                                cx.as_rust_item_ctxt(owner_id, None)
                                    .desugar_enum_def(enum_def)?,
                            ),
                        ),
                    );
                }
                hir::ItemKind::Struct(..) => {
                    let struct_def = &specs.structs[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(
                            genv.alloc(
                                cx.as_rust_item_ctxt(owner_id, None)
                                    .desugar_struct_def(struct_def)?,
                            ),
                        ),
                    );
                }
                hir::ItemKind::Trait(..) => {
                    let trait_ = &specs.traits[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(
                            genv.alloc(cx.as_rust_item_ctxt(owner_id, None).desugar_trait(trait_)?),
                        ),
                    );
                }
                hir::ItemKind::Impl(..) => {
                    let impl_ = &specs.impls[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(
                            genv.alloc(cx.as_rust_item_ctxt(owner_id, None).desugar_impl(impl_)?),
                        ),
                    );
                }
                hir::ItemKind::OpaqueTy(_) => {
                    // Opaque types are desugared as part of the desugaring of their defining function
                    span_bug!(item.span, "unexpected opaque type");
                }
                _ => {
                    span_bug!(item.span, "unsupported item");
                }
            }
        }

        rustc_hir::OwnerNode::TraitItem(trait_item) => {
            match trait_item.kind {
                rustc_hir::TraitItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx
                        .as_rust_item_ctxt(owner_id, Some(&mut opaque_tys))
                        .desugar_trait_fn(fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items().map(|(def_id, opaque_ty)| {
                        (def_id, fhir::Node::Item(genv.alloc(opaque_ty)))
                    }));
                    nodes.insert(def_id, fhir::Node::TraitItem(genv.alloc(item)));
                }
                rustc_hir::TraitItemKind::Type(..) => {
                    let item = cx
                        .as_rust_item_ctxt(owner_id, None)
                        .desugar_trait_assoc_ty()?;
                    nodes.insert(owner_id.def_id, fhir::Node::TraitItem(genv.alloc(item)));
                }
                rustc_hir::TraitItemKind::Const(..) => {
                    bug!("unsupported item");
                }
            }
        }
        rustc_hir::OwnerNode::ImplItem(impl_item) => {
            match &impl_item.kind {
                rustc_hir::ImplItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let mut opaque_tys = Default::default();
                    let item = cx
                        .as_rust_item_ctxt(owner_id, Some(&mut opaque_tys))
                        .desugar_impl_fn(fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items().map(|(def_id, opaque_ty)| {
                        (def_id, fhir::Node::Item(genv.alloc(opaque_ty)))
                    }));
                    nodes.insert(def_id, fhir::Node::ImplItem(genv.alloc(item)));
                }
                rustc_hir::ImplItemKind::Type(..) => {
                    let item = cx
                        .as_rust_item_ctxt(owner_id, None)
                        .desugar_impl_assoc_ty()?;
                    nodes.insert(owner_id.def_id, fhir::Node::ImplItem(genv.alloc(item)));
                }
                rustc_hir::ImplItemKind::Const(..) => {
                    bug!("unsupported item");
                }
            }
        }
        rustc_hir::OwnerNode::ForeignItem(_)
        | rustc_hir::OwnerNode::Crate(_)
        | rustc_hir::OwnerNode::Synthetic => {
            bug!("unsupported node");
        }
    }
    Ok(nodes)
}

struct DesugarCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    resolver_output: &'genv ResolverOutput,
}

impl<'genv, 'tcx> DesugarCtxt<'genv, 'tcx> {
    fn as_rust_item_ctxt<'a>(
        &'a self,
        owner_id: OwnerId,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::Item<'genv>>>,
    ) -> RustItemCtxt<'_, 'genv, 'tcx> {
        let owner_id = self
            .genv
            .maybe_extern_id(owner_id.def_id)
            .map(|def_id| OwnerId { def_id });
        RustItemCtxt::new(self.genv, owner_id, self.resolver_output, opaque_tys)
    }
}

fn desugar_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> fhir::Crate<'genv> {
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

fn try_desugar_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> Result<fhir::Crate<'genv>> {
    let specs = genv.collect_specs();
    let fhir = fhir::Crate::new();
    let resolver_output = genv.resolve_crate();
    let mut cx = CrateDesugar::new(genv, fhir, resolver_output);
    cx.desugar_flux_items(specs);

    if let Some(err) = cx.err {
        Err(err)
    } else {
        Ok(cx.fhir)
    }
}

macro_rules! collect_err {
    ($self:expr, $body:expr) => {
        let mut try_block = || -> std::result::Result<_, _> { $body };
        $self.err = try_block().err().or($self.err)
    };
}

struct CrateDesugar<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    fhir: fhir::Crate<'genv>,
    resolver_output: &'genv ResolverOutput,
    err: Option<ErrorGuaranteed>,
}

impl<'genv, 'tcx> CrateDesugar<'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        fhir: fhir::Crate<'genv>,
        resolver_output: &'genv ResolverOutput,
    ) -> Self {
        Self { genv, fhir, resolver_output, err: None }
    }
}

impl<'genv, 'tcx> CrateDesugar<'genv, 'tcx> {
    fn desugar_flux_items(&mut self, specs: &Specs) {
        for item in specs.flux_items_by_parent.values().flatten() {
            match item {
                surface::Item::Qualifier(qual) => {
                    collect_err!(self, self.desugar_qualifier(qual));
                }
                surface::Item::FuncDef(defn) => {
                    collect_err!(self, self.desugar_func_defn(defn));
                }
                surface::Item::SortDecl(_) => {}
            }
        }
    }

    fn desugar_func_defn(&mut self, func: &surface::SpecFunc) -> Result {
        let func = desugar::desugar_spec_func(self.genv, self.resolver_output, func)?;
        self.fhir
            .flux_items
            .insert(func.name, fhir::FluxItem::Func(func));
        Ok(())
    }

    fn desugar_qualifier(&mut self, qualifier: &surface::Qualifier) -> Result {
        let qualifier = desugar::desugar_qualifier(self.genv, self.resolver_output, qualifier)?;
        self.fhir
            .flux_items
            .insert(qualifier.name, fhir::FluxItem::Qualifier(qualifier));
        Ok(())
    }
}
