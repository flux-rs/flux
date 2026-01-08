use std::sync::OnceLock;

use flux_arc_interner::List;
use flux_common::bug;
use flux_syntax::symbols::sym;
use rustc_data_structures::unord::UnordMap;
use rustc_hir::{LangItem, def_id::DefId};
use rustc_span::{DUMMY_SP, Symbol};

use crate::{
    def_id::FluxDefId,
    global_env::GlobalEnv,
    rty::{self, AliasReft, AssocRefinements, AssocReft},
};

impl<'tcx> GlobalEnv<'_, 'tcx> {
    #[allow(
        clippy::disallowed_methods,
        reason = "this file is the source of truth for builtin assoc refts def ids"
    )]
    pub fn builtin_assoc_refts(self, def_id: DefId) -> Option<AssocRefinements> {
        static BUILTIN: OnceLock<UnordMap<DefId, AssocRefinements>> = OnceLock::new();

        BUILTIN
            .get_or_init(|| {
                let tcx = self.tcx();

                let mut map = UnordMap::default();

                // if it's a function, automatically include a no panic assoc reft if
                // the `requires` for that function includes it.
                if let Some(fn_def_id) = tcx.lang_items().fn_trait() {
                    map.insert(
                        fn_def_id,
                        AssocRefinements {
                            items: List::from_arr([AssocReft::new(
                                FluxDefId::new(fn_def_id, Symbol::intern("no_panic")),
                                false,
                                tcx.def_span(fn_def_id),
                            )]),
                        },
                    );
                }

                // Sized
                let sized_id = tcx.require_lang_item(LangItem::Sized, DUMMY_SP);
                map.insert(
                    sized_id,
                    AssocRefinements {
                        items: List::from_arr([AssocReft::new(
                            FluxDefId::new(def_id, sym::size_of),
                            false,
                            tcx.def_span(sized_id),
                        )]),
                    },
                );
                map
            })
            .get(&def_id)
            .cloned()
    }

    #[allow(
        clippy::disallowed_methods,
        reason = "this file is the source of truth for builtin assoc refts def ids"
    )]
    pub fn builtin_assoc_reft_sort(
        self,
        assoc_id: FluxDefId,
    ) -> Option<rty::EarlyBinder<rty::FuncSort>> {
        static BUILTIN: OnceLock<UnordMap<FluxDefId, rty::FuncSort>> = OnceLock::new();

        BUILTIN
            .get_or_init(|| {
                let tcx = self.tcx();

                let mut map = UnordMap::default();

                // Fn
                if let Some(no_panic_id) = tcx
                    .lang_items()
                    .fn_trait()
                    .map(|fn_def_id| FluxDefId::new(fn_def_id, Symbol::intern("no_panic")))
                {
                    map.insert(no_panic_id, rty::FuncSort::new(vec![], rty::Sort::Bool));
                }

                // Sized
                let sized_id = tcx.require_lang_item(LangItem::Sized, DUMMY_SP);
                map.insert(
                    FluxDefId::new(sized_id, sym::size_of),
                    rty::FuncSort::new(vec![], rty::Sort::Int),
                );
                map
            })
            .get(&assoc_id)
            .cloned()
            .map(rty::EarlyBinder)
    }

    pub fn builtin_assoc_reft_body(
        self,
        typing_env: rustc_middle::ty::TypingEnv<'tcx>,
        alias_reft: &AliasReft,
    ) -> rty::Lambda {
        let tcx = self.tcx();

        if tcx.is_lang_item(alias_reft.assoc_id.parent(), LangItem::Sized)
            && alias_reft.assoc_id.name() == sym::size_of
        {
            let self_ty = alias_reft.to_rustc_trait_ref(tcx).self_ty();
            let size = tcx
                .layout_of(typing_env.as_query_input(self_ty))
                .unwrap()
                .size
                .bytes();
            let body = rty::Expr::constant(rty::Constant::from(size));
            rty::Lambda::bind_with_vars(body, List::empty(), rty::Sort::Int)
        } else if alias_reft.assoc_id.name() == Symbol::intern("no_panic") {
            let body = rty::Expr::tt(); // TODO: fix!
            println!("alias reft: {:?}", alias_reft);
            rty::Lambda::bind_with_vars(body, List::empty(), rty::Sort::Bool)
        } else {
            bug!("invalid builtin assoc reft {:?}", alias_reft.assoc_id)
        }
    }
}
