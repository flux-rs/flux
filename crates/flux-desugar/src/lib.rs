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
use flux_syntax::surface;
use itertools::Itertools as _;
use rustc_data_structures::unord::UnordMap;

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;

use flux_middle::{
    ResolverOutput,
    def_id::FluxLocalDefId,
    fhir,
    global_env::GlobalEnv,
    queries::{Providers, QueryErr, QueryResult},
    query_bug,
};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::OwnerId;
use rustc_span::def_id::LocalDefId;

use crate::desugar::FluxItemCtxt;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub fn provide(providers: &mut Providers) {
    providers.resolve_crate = resolver::resolve_crate;
    providers.desugar = desugar;
    providers.fhir_attr_map = fhir_attr_map;
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

    let mut opaque_tys = Default::default();
    let node = match genv.tcx().hir_node_by_def_id(def_id) {
        rustc_hir::Node::Item(_) => {
            let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                match specs.get_item(owner_id) {
                    Some(item) => cx.desugar_item(item),
                    None => cx.lift_item(),
                }
            })?;
            fhir::Node::Item(genv.alloc(item))
        }
        rustc_hir::Node::TraitItem(_) => {
            let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                match specs.get_trait_item(owner_id) {
                    Some(item) => cx.desugar_trait_item(item),
                    None => Ok(cx.lift_trait_item()),
                }
            })?;
            fhir::Node::TraitItem(genv.alloc(item))
        }
        rustc_hir::Node::ImplItem(..) => {
            let item = cx.with_rust_item_ctxt(owner_id, Some(&mut opaque_tys), |cx| {
                match specs.get_impl_item(owner_id) {
                    Some(item) => cx.desugar_impl_item(item),
                    None => Ok(cx.lift_impl_item()),
                }
            })?;
            fhir::Node::ImplItem(genv.alloc(item))
        }
        rustc_hir::Node::AnonConst(..) => fhir::Node::AnonConst,
        rustc_hir::Node::Expr(..) => fhir::Node::Expr,
        rustc_hir::Node::ForeignItem(foreign) => {
            let item =
                cx.with_rust_item_ctxt(owner_id, None, |cx| cx.lift_foreign_item(*foreign))?;
            fhir::Node::ForeignItem(genv.alloc(item))
        }
        rustc_hir::Node::Ctor(rustc_hir::VariantData::Tuple(_, _, _)) => fhir::Node::Ctor,
        node => {
            if let Some(ident) = node.ident() {
                return Err(query_bug!(def_id, "unsupported item {ident:?}"));
            } else {
                return Err(query_bug!(def_id, "unsupported item"));
            }
        }
    };
    nodes.insert(def_id, node);
    nodes.extend(
        opaque_tys
            .into_iter()
            .map(|opaque_ty| (opaque_ty.def_id.local_id(), fhir::Node::OpaqueTy(opaque_ty))),
    );
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

#[allow(clippy::disallowed_methods, reason = "Ths is the source of truth for FluxDefId's")]
fn try_desugar_crate<'genv>(genv: GlobalEnv<'genv, '_>) -> Result<fhir::FluxItems<'genv>> {
    let specs = genv.collect_specs();
    let resolver_output = genv.resolve_crate();

    let mut fhir = fhir::FluxItems::new();
    let mut err: Option<ErrorGuaranteed> = None;
    for (parent, items) in &specs.flux_items_by_parent {
        for item in items {
            let def_id = FluxLocalDefId::new(parent.def_id, item.name().name);
            FluxItemCtxt::with(genv, resolver_output, def_id, |cx| {
                fhir.items.insert(def_id, cx.desugar_flux_item(item));
            })
            .collect_err(&mut err);
        }
    }
    err.into_result()?;

    Ok(fhir)
}

fn fhir_attr_map<'genv>(genv: GlobalEnv<'genv, '_>, def_id: LocalDefId) -> fhir::AttrMap<'genv> {
    let owner_id = OwnerId { def_id };
    let specs = genv.collect_specs();

    let (node_id, attrs) = if let Some(item) = specs.get_item(owner_id) {
        (item.node_id, &item.attrs)
    } else if let Some(impl_item) = specs.get_impl_item(owner_id) {
        (impl_item.node_id, &impl_item.attrs)
    } else if let Some(trait_item) = specs.get_trait_item(owner_id) {
        (trait_item.node_id, &trait_item.attrs)
    } else {
        return fhir::AttrMap::default();
    };

    let resolver_output = genv.resolve_crate();
    fhir::AttrMap {
        attrs: genv.alloc_slice_fill_iter(
            attrs
                .iter()
                .filter_map(|attr| {
                    match *attr {
                        surface::Attr::Trusted(trusted) => Some(fhir::Attr::Trusted(trusted)),
                        surface::Attr::TrustedImpl(trusted) => {
                            Some(fhir::Attr::TrustedImpl(trusted))
                        }
                        surface::Attr::Ignore(ignored) => Some(fhir::Attr::Ignore(ignored)),
                        surface::Attr::ProvenExternally => Some(fhir::Attr::ProvenExternally),
                        surface::Attr::ShouldFail => Some(fhir::Attr::ShouldFail),
                        surface::Attr::InferOpts(opts) => Some(fhir::Attr::InferOpts(opts)),
                        surface::Attr::NoPanic => Some(fhir::Attr::NoPanic),
                        surface::Attr::Qualifiers(_) | surface::Attr::Reveal(_) => None,
                    }
                })
                .collect_vec(),
        ),
        qualifiers: resolver_output
            .qualifier_res_map
            .get(&node_id)
            .map_or(&[][..], Vec::as_slice),
        reveals: resolver_output
            .reveal_res_map
            .get(&node_id)
            .map_or(&[][..], Vec::as_slice),
    }
}
