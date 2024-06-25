use flux_common::result::ResultExt;
use flux_middle::{global_env::GlobalEnv, pretty};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    ErrorGuaranteed, Symbol,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub fn check_impl_against_trait(genv: GlobalEnv, impl_id: LocalDefId) -> Result {
    let trait_id = genv.tcx().trait_id_of_impl(impl_id.to_def_id()).unwrap();

    let impl_assoc_refts = genv.assoc_refinements_of(impl_id).emit(&genv)?;
    let trait_assoc_refts = genv.assoc_refinements_of(trait_id).emit(&genv)?;

    for impl_assoc_reft in &impl_assoc_refts.items {
        let name = impl_assoc_reft.name;
        if trait_assoc_refts.find(name).is_none() {
            let fhir_impl_assoc_reft = genv
                .map()
                .expect_item(impl_id)
                .emit(&genv)?
                .expect_impl()
                .find_assoc_reft(name)
                .unwrap();
            return Err(genv.sess().emit_err(errors::InvalidAssocReft::new(
                fhir_impl_assoc_reft.span,
                name,
                pretty::def_id_to_string(trait_id),
            )));
        }
        check_assoc_reft(genv, impl_id, trait_id, impl_assoc_reft.name)?;
    }

    Ok(())
}

fn check_assoc_reft(genv: GlobalEnv, impl_id: LocalDefId, trait_id: DefId, name: Symbol) -> Result {
    let fake_impl_id = genv
        .get_local_id_for_extern(impl_id.to_def_id())
        .unwrap_or(impl_id);

    let impl_span = genv
        .map()
        .expect_item(fake_impl_id)
        .emit(&genv)?
        .expect_impl()
        .find_assoc_reft(name)
        .unwrap()
        .span;

    let impl_trait_ref = genv
        .impl_trait_ref(impl_id.to_def_id())
        .emit(&genv)?
        .unwrap()
        .instantiate_identity(&[]);

    let Some(impl_sort) = genv.sort_of_assoc_reft(impl_id, name).emit(genv.sess())? else {
        return Err(genv.sess().emit_err(errors::InvalidAssocReft::new(
            impl_span,
            name,
            pretty::def_id_to_string(trait_id),
        )));
    };

    let impl_sort = impl_sort.instantiate_identity(&[]);

    let Some(trait_sort) = genv.sort_of_assoc_reft(trait_id, name).emit(genv.sess())? else {
        return Err(genv.sess().emit_err(errors::InvalidAssocReft::new(
            impl_span,
            name,
            pretty::def_id_to_string(trait_id),
        )));
    };
    let trait_sort = trait_sort.instantiate(genv.tcx(), &impl_trait_ref.args, &[]);

    if impl_sort != trait_sort {
        return Err(genv
            .sess()
            .emit_err(errors::IncompatibleSort::new(impl_span, name, trait_sort, impl_sort)));
    }

    Ok(())
}

pub(crate) mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::rty;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_sort, code = E0999)]
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
    #[diag(fhir_analysis_invalid_assoc_reft, code = E0999)]
    pub struct InvalidAssocReft {
        #[primary_span]
        span: Span,
        trait_: String,
        name: Symbol,
    }

    impl InvalidAssocReft {
        pub(crate) fn new(span: Span, name: Symbol, trait_: String) -> InvalidAssocReft {
            Self { span, trait_, name }
        }
    }
}
