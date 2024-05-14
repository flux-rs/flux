//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]

#![feature(rustc_private, min_specialization, box_patterns, lazy_cell, let_chains, never_type)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::RustItemCtxt;
use flux_common::{bug, dbg};
use flux_config as config;
use flux_macros::fluent_messages;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;

use flux_middle::{
    const_eval, fhir,
    global_env::GlobalEnv,
    queries::{Providers, QueryErr, QueryResult},
    rty, ResolverOutput, Specs,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{self as hir, def_id::DefId, OwnerId};
use rustc_middle::ty::TyCtxt;
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
                    let (fn_sig, opaque_tys) = cx.desugar_fn_spec(owner_id, fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items());
                    let item = fhir::Item {
                        kind: fhir::ItemKind::Fn(fn_sig),
                        owner_id,
                        extern_id: fn_spec.extern_id,
                    };
                    nodes.insert(def_id, fhir::Node::Item(genv.alloc(item)));
                }
                hir::ItemKind::TyAlias(..) => {
                    let ty_alias = specs.ty_aliases[&owner_id].as_ref();
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.desugar_type_alias(owner_id, ty_alias)?)),
                    );
                }
                hir::ItemKind::OpaqueTy(_) => {
                    // Opaque types are desugared as part of the desugaring of their defining function
                    todo!()
                }
                hir::ItemKind::Enum(..) => {
                    let enum_def = &specs.enums[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.desugar_enum_def(owner_id, enum_def)?)),
                    );
                }
                hir::ItemKind::Struct(..) => {
                    let struct_def = &specs.structs[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.desugar_struct_def(owner_id, struct_def)?)),
                    );
                }
                hir::ItemKind::Trait(..) => {
                    let trait_ = &specs.traits[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.desugar_trait(owner_id, trait_)?)),
                    );
                }
                hir::ItemKind::Impl(..) => {
                    let impl_ = &specs.impls[&owner_id];
                    nodes.insert(
                        def_id,
                        fhir::Node::Item(genv.alloc(cx.desugar_impl(owner_id, impl_)?)),
                    );
                }
                _ => {
                    bug!("unsupported item");
                }
            }
        }
        rustc_hir::OwnerNode::TraitItem(trait_item) => {
            match trait_item.kind {
                rustc_hir::TraitItemKind::Fn(..) => {
                    let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                    let (fn_sig, opaque_tys) = cx.desugar_fn_spec(owner_id, fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items());
                    let item = fhir::TraitItem { kind: fhir::TraitItemKind::Fn(fn_sig), owner_id };
                    nodes.insert(def_id, fhir::Node::TraitItem(genv.alloc(item)));
                }
                rustc_hir::TraitItemKind::Type(..) => {
                    let assoc_ty = cx
                        .as_rust_item_ctxt(owner_id, None, None)
                        .desugar_assoc_type()?;
                    let item =
                        fhir::TraitItem { kind: fhir::TraitItemKind::Type(assoc_ty), owner_id };
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
                    let (fn_sig, opaque_tys) = cx.desugar_fn_spec(owner_id, fn_spec)?;
                    nodes.extend_unord(opaque_tys.into_items());
                    let item = fhir::ImplItem {
                        kind: fhir::ImplItemKind::Fn(fn_sig),
                        owner_id,
                        extern_id: fn_spec.extern_id,
                    };
                    nodes.insert(def_id, fhir::Node::ImplItem(genv.alloc(item)));
                }
                rustc_hir::ImplItemKind::Type(..) => {
                    let assoc_ty = cx
                        .as_rust_item_ctxt(owner_id, None, None)
                        .desugar_assoc_type()?;
                    let item = fhir::ImplItem {
                        kind: fhir::ImplItemKind::Type(assoc_ty),
                        owner_id,
                        extern_id: None,
                    };
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
        extern_id: Option<DefId>,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    ) -> RustItemCtxt<'_, 'genv, 'tcx> {
        RustItemCtxt::new(self.genv, owner_id, extern_id, self.resolver_output, opaque_tys)
    }

    fn desugar_fn_spec(
        &self,
        owner_id: OwnerId,
        fn_spec: &surface::FnSpec,
    ) -> QueryResult<(fhir::FnSig<'genv>, UnordMap<LocalDefId, fhir::Node<'genv>>)> {
        let mut opaque_tys = Default::default();
        let fn_sig = self
            .as_rust_item_ctxt(owner_id, fn_spec.extern_id, Some(&mut opaque_tys))
            .desugar_fn_sig(fn_spec)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", fn_sig).unwrap();
        }

        let opaque_tys: UnordMap<_, _> = opaque_tys
            .into_items()
            .map(|(def_id, opaque_ty)| {
                let owner_id = OwnerId { def_id };
                let item = fhir::Item {
                    kind: fhir::ItemKind::OpaqueTy(opaque_ty),
                    owner_id,
                    extern_id: None,
                };
                (def_id, fhir::Node::Item(self.genv.alloc(item)))
            })
            .collect();

        Ok((fn_sig, opaque_tys))
    }

    fn desugar_enum_def(
        &self,
        owner_id: OwnerId,
        enum_def: &surface::EnumDef,
    ) -> QueryResult<fhir::Item<'genv>> {
        let extern_id = enum_def.extern_id;
        let enum_def = self
            .as_rust_item_ctxt(owner_id, extern_id, None)
            .desugar_enum_def(enum_def)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", &enum_def).unwrap();
        }

        Ok(fhir::Item { kind: fhir::ItemKind::Enum(enum_def), owner_id, extern_id })
    }

    fn desugar_struct_def(
        &self,
        owner_id: OwnerId,
        struct_def: &surface::StructDef,
    ) -> QueryResult<fhir::Item<'genv>> {
        let extern_id = struct_def.extern_id;
        let struct_def = self
            .as_rust_item_ctxt(owner_id, extern_id, None)
            .desugar_struct_def(struct_def)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", struct_def).unwrap();
        }

        Ok(fhir::Item { kind: fhir::ItemKind::Struct(struct_def), owner_id, extern_id })
    }

    fn desugar_type_alias(
        &self,
        owner_id: OwnerId,
        ty_alias: Option<&surface::TyAlias>,
    ) -> QueryResult<fhir::Item<'genv>> {
        let ty_alias = self
            .as_rust_item_ctxt(owner_id, None, None)
            .desugar_type_alias(ty_alias)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", &ty_alias).unwrap();
        }

        Ok(fhir::Item { kind: fhir::ItemKind::TyAlias(ty_alias), owner_id, extern_id: None })
    }

    fn desugar_trait(
        &self,
        owner_id: OwnerId,
        trait_: &surface::Trait,
    ) -> QueryResult<fhir::Item<'genv>> {
        let trait_ = self
            .as_rust_item_ctxt(owner_id, None, None)
            .desugar_trait(trait_)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", &trait_).unwrap();
        }

        Ok(fhir::Item { kind: fhir::ItemKind::Trait(trait_), owner_id, extern_id: None })
    }

    fn desugar_impl(
        &self,
        owner_id: OwnerId,
        impl_: &surface::Impl,
    ) -> QueryResult<fhir::Item<'genv>> {
        let impl_ = self
            .as_rust_item_ctxt(owner_id, None, None)
            .desugar_impl(impl_)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id.def_id, "fhir", &impl_).unwrap();
        }

        Ok(fhir::Item { kind: fhir::ItemKind::Impl(impl_), owner_id, extern_id: None })
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
        for defn in &specs.func_defs {
            collect_err!(self, self.desugar_func_defn(defn));
        }

        for def_id in &specs.consts {
            collect_err!(self, self.desugar_const(*def_id));
        }

        for qualifier in &specs.qualifs {
            collect_err!(self, self.desugar_qualifier(qualifier));
        }
    }

    fn desugar_const(&mut self, def_id: LocalDefId) -> Result<rty::Constant> {
        let ty = self.genv.tcx().type_of(def_id).instantiate_identity();
        if let Ok(const_result) = self.genv.tcx().const_eval_poly(def_id.to_def_id())
            && let Some(val) = const_result.try_to_scalar_int()
            && let Some(val) = const_eval::scalar_int_to_rty_constant(self.genv.tcx(), val, ty)
        {
            let sym = def_id_symbol(self.genv.tcx(), def_id);
            self.fhir
                .consts
                .insert(sym, fhir::ConstInfo { def_id: def_id.to_def_id(), sym, val });
            Ok(val)
        } else {
            let span = self.genv.tcx().def_span(def_id);
            Err(self
                .genv
                .sess()
                .emit_err(errors::InvalidConstant::new(span)))
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

fn def_id_symbol(tcx: TyCtxt, def_id: LocalDefId) -> rustc_span::Symbol {
    let did = def_id.to_def_id();
    // TODO(RJ) use fully qualified names: Symbol::intern(&tcx.def_path_str(did))
    let def_path = tcx.def_path(did);
    if let Some(dp) = def_path.data.last() {
        if let rustc_hir::definitions::DefPathData::ValueNs(sym) = dp.data {
            return sym;
        }
    }
    panic!("def_id_symbol fails on {did:?}")
}
