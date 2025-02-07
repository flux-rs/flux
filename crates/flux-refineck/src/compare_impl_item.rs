use flux_common::result::ErrorEmitter;
use flux_infer::{
    infer::{GlobalEnvExt as _, InferCtxt},
    projections::NormalizeExt as _,
};
use flux_middle::{
    def_id_to_string, global_env::GlobalEnv, queries::QueryResult, rty::TraitRef, MaybeExternId,
};
use rustc_hash::FxHashSet;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::TypingMode;
use rustc_span::{def_id::DefId, Symbol};

pub fn check_impl_against_trait(genv: GlobalEnv, impl_id: MaybeExternId) -> QueryResult {
    let trait_id = genv.tcx().trait_id_of_impl(impl_id.resolved_id()).unwrap();

    let impl_assoc_refts = genv.assoc_refinements_of(impl_id)?;
    let trait_assoc_refts = genv.assoc_refinements_of(trait_id)?;
    let impl_names: FxHashSet<_> = impl_assoc_refts.items.iter().map(|x| x.name).collect();

    for trait_assoc_reft in &trait_assoc_refts.items {
        let name = trait_assoc_reft.name;
        let has_default = genv.default_assoc_refinement_def(trait_id, name)?.is_some();
        if !impl_names.contains(&name) && !has_default {
            let span = genv.tcx().def_span(impl_id);
            Err(genv.emit(errors::MissingAssocReft::new(span, name, def_id_to_string(trait_id))))?;
        }
    }

    let impl_trait_ref = genv
        .impl_trait_ref(impl_id.resolved_id())?
        .unwrap()
        .instantiate_identity();

    let mut root_ctxt = genv
        .infcx_root(trait_id, genv.infer_opts(impl_id.local_id()))
        .with_generic_args(&impl_trait_ref.args)
        .build()?;
    let rustc_infcx = genv
        .tcx()
        .infer_ctxt()
        .build(TypingMode::non_body_analysis());
    let mut infcx = root_ctxt.infcx(trait_id, &rustc_infcx);

    for impl_assoc_reft in &impl_assoc_refts.items {
        let name = impl_assoc_reft.name;
        if trait_assoc_refts.find(name).is_none() {
            let fhir_impl_assoc_reft = genv
                .map()
                .expect_item(impl_id.local_id())?
                .expect_impl()
                .find_assoc_reft(name)
                .unwrap();
            Err(genv.emit(errors::InvalidAssocReft::new(
                fhir_impl_assoc_reft.span,
                name,
                def_id_to_string(trait_id),
            )))?;
        }
        check_assoc_reft(&mut infcx, impl_id, &impl_trait_ref, trait_id, impl_assoc_reft.name)?;
    }

    Ok(())
}

fn check_assoc_reft(
    infcx: &mut InferCtxt,
    impl_id: MaybeExternId,
    impl_trait_ref: &TraitRef,
    trait_id: DefId,
    name: Symbol,
) -> QueryResult {
    let impl_span = infcx
        .genv
        .map()
        .expect_item(impl_id.local_id())?
        .expect_impl()
        .find_assoc_reft(name)
        .unwrap()
        .span;

    let Some(impl_sort) = infcx.genv.sort_of_assoc_reft(impl_id, name)? else {
        return Err(infcx.genv.emit(errors::InvalidAssocReft::new(
            impl_span,
            name,
            def_id_to_string(trait_id),
        )))?;
    };

    let impl_sort = impl_sort
        .instantiate_identity()
        .normalize_projections(infcx)?;

    let Some(trait_sort) = infcx.genv.sort_of_assoc_reft(trait_id, name)? else {
        return Err(infcx.genv.emit(errors::InvalidAssocReft::new(
            impl_span,
            name,
            def_id_to_string(trait_id),
        )))?;
    };
    let trait_sort = trait_sort
        .instantiate(infcx.tcx(), &impl_trait_ref.args, &[])
        .normalize_projections(infcx)?;

    if impl_sort != trait_sort {
        Err(infcx
            .genv
            .emit(errors::IncompatibleSort::new(impl_span, name, trait_sort, impl_sort)))?;
    }

    Ok(())
}

pub(crate) mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::rty;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(refineck_incompatible_sort, code = E0999)]
    pub(super) struct IncompatibleSort {
        #[primary_span]
        #[label]
        span: Span,
        name: Symbol,
        expected: rty::FuncSort,
        found: rty::FuncSort,
    }

    impl IncompatibleSort {
        pub(super) fn new(
            span: Span,
            name: Symbol,
            expected: rty::FuncSort,
            found: rty::FuncSort,
        ) -> Self {
            Self { span, name, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(refineck_missing_assoc_reft, code = E0999)]
    pub struct MissingAssocReft {
        #[primary_span]
        span: Span,
        trait_: String,
        name: Symbol,
    }

    impl MissingAssocReft {
        pub(crate) fn new(span: Span, name: Symbol, trait_: String) -> Self {
            Self { span, trait_, name }
        }
    }

    #[derive(Diagnostic)]
    #[diag(refineck_invalid_assoc_reft, code = E0999)]
    pub struct InvalidAssocReft {
        #[primary_span]
        span: Span,
        trait_: String,
        name: Symbol,
    }

    impl InvalidAssocReft {
        pub(crate) fn new(span: Span, name: Symbol, trait_: String) -> Self {
            Self { span, trait_, name }
        }
    }
}
