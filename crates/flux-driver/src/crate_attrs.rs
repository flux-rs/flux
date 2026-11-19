//! Injection of the crate-level attributes Flux needs.
//!
//! Flux needs `#![feature(register_tool, custom_inner_attributes)]`, `#![register_tool(flux)]`
//! and `#![register_tool(flux_tool)]`. We used to pass them unconditionally with `-Zcrate-attr`,
//! but that fails with `duplicate_features` on crates that already enable the features
//! themselves (e.g., `core`). Instead, we inject them right after parsing the crate root, skipping
//! those the crate already declares, either directly or through a `cfg_attr` whose predicate
//! holds.
//!
//! Crate-level `cfg_attr`s are expanded by rustc right after the `after_crate_root_parsing`
//! callback, and the set of enabled features is computed from the result. There is no later hook
//! where we could inspect the expanded attributes and still inject new ones, so we expand them
//! ourselves with [`pre_configure_attrs`], the same function rustc uses. Any diagnostic it emits
//! (e.g., for a malformed `cfg_attr`) is emitted again, identically, when rustc calls it, and
//! rustc deduplicates identical diagnostics, so they are only reported once.

use rustc_ast as ast;
use rustc_expand::config::pre_configure_attrs;
use rustc_session::Session;
use rustc_span::{Symbol, sym};

const FEATURES: [&str; 2] = ["register_tool", "custom_inner_attributes"];
const TOOLS: [&str; 2] = ["flux", "flux_tool"];

pub(crate) fn inject(sess: &Session, krate: &mut ast::Crate) {
    let crate_attrs = pre_configure_attrs(sess, &krate.attrs);

    let declared = |attr_name: Symbol, name: &str| {
        crate_attrs.iter().any(|attr| {
            attr.style == ast::AttrStyle::Inner
                && attr.has_name(attr_name)
                && attr.meta_item_list().is_some_and(|items| {
                    items
                        .iter()
                        .any(|it| it.ident().is_some_and(|id| id.name.as_str() == name))
                })
        })
    };

    let missing_features: Vec<&str> = FEATURES
        .into_iter()
        .filter(|feature| !declared(sym::feature, feature))
        .collect();
    let mut attrs = vec![];
    if !missing_features.is_empty() {
        attrs.push(format!("feature({})", missing_features.join(", ")));
    }
    for tool in TOOLS {
        if !declared(sym::register_tool, tool) {
            attrs.push(format!("register_tool({tool})"));
        }
    }
    rustc_builtin_macros::cmdline_attrs::inject(krate, &sess.psess, &attrs);
}
