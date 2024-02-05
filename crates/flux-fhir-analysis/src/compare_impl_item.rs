use flux_errors::ResultExt as _;
use flux_middle::{global_env::GlobalEnv, pretty};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    ErrorGuaranteed, Symbol,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub fn check_impl_against_trait(genv: GlobalEnv, impl_id: LocalDefId) -> Result {
    let trait_id = genv.tcx().trait_id_of_impl(impl_id.to_def_id()).unwrap();

    let impl_assoc_preds = genv.assoc_predicates_of(impl_id);
    let trait_assoc_preds = genv.assoc_predicates_of(trait_id);

    for impl_assoc_pred in &impl_assoc_preds.predicates {
        let name = impl_assoc_pred.name;
        if trait_assoc_preds.find(name).is_none() {
            let fhir_impl_assoc_pred = genv
                .map()
                .expect_item(impl_id)
                .expect_impl()
                .find_assoc_predicate(name)
                .unwrap();
            return Err(genv.sess().emit_err(errors::InvalidAssocPredicate::new(
                fhir_impl_assoc_pred.span,
                name,
                pretty::def_id_to_string(trait_id),
            )));
        }
        check_assoc_predicate(genv, impl_id, trait_id, impl_assoc_pred.name)?;
    }

    Ok(())
}

fn check_assoc_predicate(
    genv: GlobalEnv,
    impl_id: LocalDefId,
    trait_id: DefId,
    name: Symbol,
) -> Result {
    let fake_impl_id = genv
        .map()
        .get_local_id_for_extern(impl_id.into())
        .unwrap_or(impl_id);

    let impl_span = genv
        .map()
        .expect_item(fake_impl_id)
        .expect_impl()
        .find_assoc_predicate(name)
        .unwrap()
        .span;

    let impl_trait_ref = genv
        .impl_trait_ref(impl_id.to_def_id())
        .emit(genv.sess())?
        .unwrap()
        .instantiate_identity(&[]);

    let Some(impl_sort) = genv.sort_of_assoc_pred(impl_id.to_def_id(), name) else {
        return Err(genv.sess().emit_err(errors::InvalidAssocPredicate::new(
            impl_span,
            name,
            pretty::def_id_to_string(trait_id),
        )));
    };

    let impl_sort = impl_sort.instantiate_identity(&[]);

    let Some(trait_sort) = genv.sort_of_assoc_pred(trait_id, name) else {
        return Err(genv.sess().emit_err(errors::InvalidAssocPredicate::new(
            impl_span,
            name,
            pretty::def_id_to_string(trait_id),
        )));
    };
    let trait_sort = trait_sort.instantiate(&impl_trait_ref.args, &[]);

    if impl_sort != trait_sort {
        return Err(genv
            .sess()
            .emit_err(errors::IncompatibleSort::new(impl_span, name, trait_sort, impl_sort)));
    }

    Ok(())
}

pub(crate) mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::rty;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_sort, code = "FLUX")]
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
    #[diag(fhir_analysis_invalid_assoc_predicate, code = "FLUX")]
    pub struct InvalidAssocPredicate {
        #[primary_span]
        span: Span,
        trait_id: String,
        name: Symbol,
    }

    impl InvalidAssocPredicate {
        pub(crate) fn new(span: Span, name: Symbol, trait_id: String) -> InvalidAssocPredicate {
            Self { span, trait_id, name }
        }
    }
}
