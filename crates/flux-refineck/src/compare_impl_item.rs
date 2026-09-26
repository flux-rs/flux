use flux_common::result::ErrorEmitter;
use flux_infer::{infer::GlobalEnvExt as _, projections::NormalizeExt as _};
use flux_middle::{
    def_id::{FluxId, MaybeExternId},
    def_id_to_string,
    global_env::GlobalEnv,
    queries::QueryResult,
    query_bug,
};
use rustc_data_structures::unord::UnordSet;
use rustc_infer::infer::TyCtxtInferExt as _;
use rustc_middle::ty::TypingMode;

pub fn check_impl_against_trait(genv: GlobalEnv, impl_id: MaybeExternId) -> QueryResult {
    let trait_id = genv.tcx().impl_trait_id(impl_id.resolved_id());

    let impl_assoc_refts = genv.assoc_refinements_of(impl_id)?;
    let trait_assoc_refts = genv.assoc_refinements_of(trait_id)?;
    let impl_names: UnordSet<_> = impl_assoc_refts.items.iter().map(|x| x.name()).collect();

    for trait_assoc_reft in &trait_assoc_refts.items {
        let trait_assoc_def_id = trait_assoc_reft.def_id();
        let has_default = genv
            .default_assoc_refinement_body(trait_assoc_def_id)?
            .is_some();
        if !impl_names.contains(&trait_assoc_reft.name()) && !has_default {
            let span = genv.tcx().def_span(impl_id);
            Err(genv.emit(errors::MissingAssocReft::new(span, trait_assoc_reft.name())))?;
        } else if impl_names.contains(&trait_assoc_reft.name()) && trait_assoc_reft.final_ {
            let span = genv.tcx().def_span(impl_id);
            Err(genv.emit(errors::ImplAssocReftOnFinal::new(span, trait_assoc_reft.name())))?;
        }
    }

    for impl_assoc_reft in &impl_assoc_refts.items {
        let name = impl_assoc_reft.name();
        if trait_assoc_refts.find(name).is_some() {
            genv.compare_impl_assoc_reft(impl_assoc_reft.def_id())?;
        } else {
            let fhir_impl_assoc_reft = genv
                .fhir_expect_item(impl_id.local_id())?
                .expect_impl()
                .find_assoc_reft(name)
                .unwrap();
            Err(genv.emit(errors::InvalidAssocReft::new(
                fhir_impl_assoc_reft.span,
                name,
                def_id_to_string(trait_id),
            )))?;
        }
    }

    Ok(())
}

/// Checks that the sort of an associated refinement defined in a trait implementation matches the
/// sort of the corresponding associated refinement in the trait.
///
/// This is a query so that the check runs (and reports errors) exactly once, regardless of whether
/// it is triggered while checking the implementation or when an associated refinement is
/// normalized to the implementation's body at a use site.
pub(crate) fn compare_impl_assoc_reft(
    genv: GlobalEnv,
    impl_assoc_id: FluxId<MaybeExternId>,
) -> QueryResult {
    let impl_id = impl_assoc_id.parent();
    let name = impl_assoc_id.name();

    let Some(impl_assoc_reft) = genv.assoc_refinements_of(impl_id)?.find(name) else {
        return Err(query_bug!(impl_id.resolved_id(), "associated refinement `{name}` not found"));
    };

    let trait_id = genv.tcx().impl_trait_id(impl_id.resolved_id());
    let Some(trait_assoc_reft) = genv.assoc_refinements_of(trait_id)?.find(name) else {
        // The associated refinement is not a member of the trait. This is reported when checking
        // the implementation and it is never used to normalize a trait's associated refinement.
        return Ok(());
    };

    let impl_span = genv
        .fhir_expect_item(impl_id.local_id())?
        .expect_impl()
        .find_assoc_reft(name)
        .unwrap()
        .span;

    let impl_trait_ref = genv
        .impl_trait_ref(impl_id.resolved_id())?
        .instantiate_identity();

    let rustc_infcx = genv
        .tcx()
        .infer_ctxt()
        .with_next_trait_solver(true)
        .build(TypingMode::non_body_analysis());
    let mut root_ctxt = genv
        .infcx_root(&rustc_infcx, genv.infer_opts(impl_id.local_id()))
        .with_const_generics(impl_id.resolved_id())?
        .build()?;
    let mut infcx = root_ctxt.infcx(impl_id.resolved_id(), &rustc_infcx);

    let impl_sort = genv
        .sort_of_assoc_reft(impl_assoc_reft.def_id())?
        .instantiate_identity()
        .deeply_normalize(&mut infcx.at(impl_span))?;

    let trait_sort = genv
        .sort_of_assoc_reft(trait_assoc_reft.def_id())?
        .instantiate(genv.tcx(), &impl_trait_ref.args, &[])
        .deeply_normalize(&mut infcx.at(impl_span))?;

    if impl_sort != trait_sort {
        Err(genv.emit(errors::IncompatibleSort::new(impl_span, name, trait_sort, impl_sort)))?;
    }

    Ok(())
}

pub(crate) mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::rty;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag("implemented associated refinement `{$name}` has an incompatible sort for trait", code = E0999)]
    pub(super) struct IncompatibleSort {
        #[primary_span]
        #[label("expected `{$expected}`, found `{$found}`")]
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
    #[diag("associated refinement `{$name}` is missing from implementation", code = E0999)]
    pub struct MissingAssocReft {
        #[primary_span]
        span: Span,
        name: Symbol,
    }

    impl MissingAssocReft {
        pub(crate) fn new(span: Span, name: Symbol) -> Self {
            Self { span, name }
        }
    }

    #[derive(Diagnostic)]
    #[diag("associated refinement `{$name}` is final and should not be implemented anywhere other than the trait definition", code = E0999)]
    pub struct ImplAssocReftOnFinal {
        #[primary_span]
        span: Span,
        name: Symbol,
    }

    impl ImplAssocReftOnFinal {
        pub(crate) fn new(span: Span, name: Symbol) -> Self {
            Self { span, name }
        }
    }

    #[derive(Diagnostic)]
    #[diag("associated refinement `{$name}` is not a member of trait `{$trait_}`", code = E0999)]
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
