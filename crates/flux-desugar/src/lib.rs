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
use rustc_hir::OwnerId;
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
                    surface::FluxItem::Qualifier(qual) => {
                        self.desugar_qualifier(def_id, qual)
                            .collect_err(&mut self.err);
                    }
                    surface::FluxItem::FuncDef(defn) => {
                        self.desugar_func_defn(def_id, defn)
                            .collect_err(&mut self.err);
                    }
                    surface::FluxItem::SortDecl(_) => {}
                    surface::FluxItem::PrimOpProp(primop_prop) => {
                        self.desugar_primop_prop(def_id, primop_prop)
                            .collect_err(&mut self.err);
                    }
                }
            }
        }
    }

    fn desugar_primop_prop(
        &mut self,
        def_id: FluxLocalDefId,
        prop: &surface::PrimOpProp,
    ) -> Result {
        let prop = desugar::desugar_primop_prop(self.genv, self.resolver_output, def_id, prop)?;
        self.fhir
            .items
            .insert(def_id, fhir::FluxItem::PrimOpProp(self.genv.alloc(prop)));
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
