//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]

#![feature(rustc_private, min_specialization, box_patterns, lazy_cell, let_chains, never_type)]

extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use desugar::RustItemCtxt;
use flux_common::dbg;
use flux_config as config;
use flux_macros::fluent_messages;
use rustc_data_structures::unord::{ExtendUnord, UnordMap};
use rustc_errors::{DiagnosticMessage, SubdiagnosticMessage};

fluent_messages! { "../locales/en-US.ftl" }

mod desugar;
mod errors;
pub mod resolver;

use flux_middle::{
    const_eval, fhir, global_env::GlobalEnv, queries::Providers, rty, ResolverOutput, Specs,
};
use flux_syntax::surface;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{self as hir, OwnerId};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub fn provide(providers: &mut Providers) {
    providers.resolve_crate = resolver::resolve_crate;
    providers.fhir_crate = desugar_crate;
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
    let fhir = fhir::Crate::new(specs.ignores.clone(), specs.crate_config);
    let resolver_output = genv.resolve_crate();
    let mut cx = CrateDesugar::new(genv, fhir, resolver_output);
    cx.desugar_flux_items(specs);
    cx.desugar_rust_items(specs);

    for (extern_def_id, local_def_id) in &specs.extern_specs {
        cx.fhir.externs.insert(*extern_def_id, *local_def_id);
    }

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

    fn desugar_rust_items(&mut self, specs: &Specs) {
        let crate_items = self.genv.tcx().hir_crate_items(());
        for owner_id in crate_items.owners() {
            match self.genv.hir().owner(owner_id) {
                rustc_hir::OwnerNode::Item(item) => {
                    self.desugar_rust_item(item, specs);
                }
                rustc_hir::OwnerNode::TraitItem(trait_item) => {
                    self.desugar_trait_item(trait_item, specs);
                }
                rustc_hir::OwnerNode::ImplItem(impl_item) => {
                    self.desugar_impl_item(impl_item, specs);
                }
                rustc_hir::OwnerNode::ForeignItem(_) | rustc_hir::OwnerNode::Crate(_) => {}
            }
        }
    }

    fn desugar_rust_item(&mut self, item: &hir::Item, specs: &Specs) {
        let owner_id = item.owner_id;

        match item.kind {
            hir::ItemKind::Fn(..) => {
                let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                collect_err!(self, self.desugar_item_fn(owner_id, fn_spec));
            }
            hir::ItemKind::TyAlias(..) => {
                let ty_alias = specs.ty_aliases[&owner_id].as_ref();
                collect_err!(self, self.desugar_type_alias(owner_id, ty_alias));
            }
            hir::ItemKind::OpaqueTy(_) => {
                // Opaque types are desugared as part of the desugaring of their defining function
            }
            hir::ItemKind::Enum(..) => {
                let enum_def = &specs.enums[&owner_id];
                collect_err!(self, self.desugar_enum_def(owner_id, enum_def));
            }
            hir::ItemKind::Struct(..) => {
                let struct_def = &specs.structs[&owner_id];
                collect_err!(self, self.desugar_struct_def(owner_id, struct_def));
            }
            hir::ItemKind::Trait(..) => {
                collect_err!(self, self.desugar_trait(owner_id, &specs.traits[&owner_id]));
            }
            hir::ItemKind::Impl(..) => {
                collect_err!(self, self.desugar_impl(owner_id, &specs.impls[&owner_id]));
            }
            _ => {}
        }
    }

    fn desugar_trait_item(&mut self, trait_item: &hir::TraitItem, specs: &Specs) {
        let owner_id = trait_item.owner_id;
        match trait_item.kind {
            rustc_hir::TraitItemKind::Fn(..) => {
                let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                collect_err!(self, self.desugar_trait_fn(owner_id, fn_spec));
            }
            rustc_hir::TraitItemKind::Type(..) => {
                collect_err!(self, {
                    let assoc_ty = self
                        .as_rust_item_ctxt(owner_id, None)
                        .desugar_assoc_type()?;
                    let trait_item = fhir::TraitItem { kind: fhir::TraitItemKind::Type(assoc_ty) };
                    self.fhir.trait_items.insert(owner_id.def_id, trait_item);
                    Ok(())
                });
            }
            rustc_hir::TraitItemKind::Const(_, _) => {}
        }
    }

    fn desugar_impl_item(&mut self, impl_item: &hir::ImplItem, specs: &Specs) {
        let owner_id = impl_item.owner_id;
        match &impl_item.kind {
            rustc_hir::ImplItemKind::Fn(..) => {
                let fn_spec = specs.fn_sigs.get(&owner_id).unwrap();
                collect_err!(self, self.desugar_impl_fn(owner_id, fn_spec));
            }
            rustc_hir::ImplItemKind::Type(..) => {
                collect_err!(self, {
                    let assoc_ty = self
                        .as_rust_item_ctxt(owner_id, None)
                        .desugar_assoc_type()?;
                    let impl_item = fhir::ImplItem { kind: fhir::ImplItemKind::Type(assoc_ty) };
                    self.fhir.impl_items.insert(owner_id.def_id, impl_item);
                    Ok(())
                });
            }
            rustc_hir::ImplItemKind::Const(_, _) => {}
        }
    }

    pub fn desugar_struct_def(
        &mut self,
        owner_id: OwnerId,
        struct_def: &surface::StructDef,
    ) -> Result {
        let def_id = owner_id.def_id;

        let struct_def = self
            .as_rust_item_ctxt(owner_id, None)
            .desugar_struct_def(struct_def)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id, "fhir", struct_def).unwrap();
        }

        let item = fhir::Item { kind: fhir::ItemKind::Struct(struct_def) };
        self.fhir.items.insert(def_id, item);

        Ok(())
    }

    pub fn desugar_enum_def(&mut self, owner_id: OwnerId, enum_def: &surface::EnumDef) -> Result {
        let def_id = owner_id.def_id;

        let enum_def = self
            .as_rust_item_ctxt(owner_id, None)
            .desugar_enum_def(enum_def)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id, "fhir", &enum_def).unwrap();
        }

        let item = fhir::Item { kind: fhir::ItemKind::Enum(enum_def) };
        self.fhir.items.insert(def_id, item);

        Ok(())
    }

    pub fn desugar_type_alias(
        &mut self,
        owner_id: OwnerId,
        ty_alias: Option<&surface::TyAlias>,
    ) -> Result {
        let def_id = owner_id.def_id;

        let ty_alias = self
            .as_rust_item_ctxt(owner_id, None)
            .desugar_type_alias(ty_alias)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), owner_id, "fhir", &ty_alias).unwrap();
        }

        let item = fhir::Item { kind: fhir::ItemKind::TyAlias(ty_alias) };
        self.fhir.items.insert(def_id, item);

        Ok(())
    }

    fn desugar_item_fn(&mut self, owner_id: OwnerId, fn_spec: &surface::FnSpec) -> Result {
        let fn_sig = self.desugar_fn_spec(owner_id, fn_spec)?;

        let item = fhir::Item { kind: fhir::ItemKind::Fn(fn_sig) };
        self.fhir.items.insert(owner_id.def_id, item);
        Ok(())
    }

    fn desugar_impl_fn(&mut self, owner_id: OwnerId, fn_spec: &surface::FnSpec) -> Result {
        let fn_sig = self.desugar_fn_spec(owner_id, fn_spec)?;

        let impl_item = fhir::ImplItem { kind: fhir::ImplItemKind::Fn(fn_sig) };
        self.fhir.impl_items.insert(owner_id.def_id, impl_item);

        Ok(())
    }

    fn desugar_trait_fn(&mut self, owner_id: OwnerId, fn_spec: &surface::FnSpec) -> Result {
        let fn_sig = self.desugar_fn_spec(owner_id, fn_spec)?;

        let trait_item = fhir::TraitItem { kind: fhir::TraitItemKind::Fn(fn_sig) };
        self.fhir.trait_items.insert(owner_id.def_id, trait_item);

        Ok(())
    }

    fn desugar_fn_spec(
        &mut self,
        owner_id: OwnerId,
        fn_spec: &surface::FnSpec,
    ) -> Result<fhir::FnSig<'genv>> {
        let def_id = owner_id.def_id;

        if let Some(quals) = &fn_spec.qual_names {
            self.fhir
                .fn_quals
                .insert(def_id, self.genv.alloc_slice(&quals.names));
        }

        let mut opaque_tys = Default::default();
        let fn_sig = self
            .as_rust_item_ctxt(owner_id, Some(&mut opaque_tys))
            .desugar_fn_sig(fn_spec)?;

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), def_id, "fhir", fn_sig).unwrap();
        }

        self.fhir
            .items
            .extend_unord(opaque_tys.into_items().map(|(def_id, opaque_ty)| {
                (def_id, fhir::Item { kind: fhir::ItemKind::OpaqueTy(opaque_ty) })
            }));

        Ok(fn_sig)
    }

    pub fn desugar_trait(&mut self, owner_id: OwnerId, trait_: &surface::Trait) -> Result {
        let def_id = owner_id.def_id;

        let trait_ = self
            .as_rust_item_ctxt(owner_id, None)
            .desugar_trait(trait_)?;

        let item = fhir::Item { kind: fhir::ItemKind::Trait(trait_) };
        self.fhir.items.insert(def_id, item);

        Ok(())
    }

    pub fn desugar_impl(&mut self, owner_id: OwnerId, impl_: &surface::Impl) -> Result {
        let def_id = owner_id.def_id;

        let impl_ = self.as_rust_item_ctxt(owner_id, None).desugar_impl(impl_)?;

        let item = fhir::Item { kind: fhir::ItemKind::Impl(impl_) };
        self.fhir.items.insert(def_id, item);

        Ok(())
    }

    fn as_rust_item_ctxt<'a>(
        &'a self,
        owner_id: OwnerId,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::OpaqueTy<'genv>>>,
    ) -> RustItemCtxt<'_, 'genv, 'tcx> {
        RustItemCtxt::new(self.genv, owner_id, self.resolver_output, opaque_tys)
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
