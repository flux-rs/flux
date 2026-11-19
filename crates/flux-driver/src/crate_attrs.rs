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
//! where we could inspect the expanded attributes and still inject new ones, so we evaluate the
//! `cfg_attr`s ourselves. We use rustc's public parsing and evaluation APIs, but with
//! [`ShouldEmit::Nothing`] so that a malformed `cfg_attr` is only reported once, by rustc.

use rustc_ast::{
    self as ast, AttrArgs, AttrItem, AttrKind, AttrStyle, CRATE_NODE_ID, DelimArgs,
    token::Delimiter,
};
use rustc_attr_ir::{
    AttrPath, CfgEntry,
    target::{AstTarget, Target},
};
use rustc_attr_parsing::{
    AttributeParser, AttributeSafety, CFG_TEMPLATE, ParsedDescription, ShouldEmit,
    eval_config_entry,
    parser::{AllowExprMetavar, MetaItemOrLitParser},
};
use rustc_errors::PResult;
use rustc_parse::{
    exp,
    parser::{ForceCollect, Parser},
};
use rustc_session::Session;
use rustc_span::{ErrorGuaranteed, Symbol, sym};

const FEATURES: [&str; 2] = ["register_tool", "custom_inner_attributes"];
const TOOLS: [&str; 2] = ["flux", "flux_tool"];

pub(crate) fn inject(sess: &Session, krate: &mut ast::Crate) {
    let mut crate_attrs = vec![];
    for attr in &krate.attrs {
        if attr.style == AttrStyle::Inner
            && let AttrKind::Normal(normal) = &attr.kind
        {
            expand_cfg_attr(sess, &normal.item, &mut crate_attrs);
        }
    }

    let declared = |attr_name: Symbol, name: &str| {
        crate_attrs.iter().any(|item| {
            item.path == attr_name
                && item.meta_item_list().is_some_and(|items| {
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

/// Pushes `item` into `out`, or, if it is a `cfg_attr` whose predicate holds, the attributes it
/// expands to (recursively). Malformed `cfg_attr`s are silently ignored; rustc reports them later.
fn expand_cfg_attr(sess: &Session, item: &AttrItem, out: &mut Vec<AttrItem>) {
    if item.path != sym::cfg_attr {
        out.push(item.clone());
        return;
    }
    let AttrArgs::Delimited(DelimArgs { delim: Delimiter::Parenthesis, tokens, .. }) = &item.args
    else {
        return;
    };
    let Some((pred, inner)) = parse_cfg_attr_silently(sess, item, tokens.clone()) else {
        return;
    };
    if eval_config_entry(sess, &pred).as_bool() {
        for inner in inner {
            expand_cfg_attr(sess, &inner, out);
        }
    }
}

/// Parses the arguments of a `cfg_attr`, i.e., `predicate, attr1, attr2, ...`, without emitting
/// any diagnostics. This mirrors [`rustc_attr_parsing::parse_cfg_attr`], which always emits them.
fn parse_cfg_attr_silently(
    sess: &Session,
    item: &AttrItem,
    tokens: rustc_ast::tokenstream::TokenStream,
) -> Option<(CfgEntry, Vec<AttrItem>)> {
    let mut parser = Parser::new(&sess.psess, tokens, Some("`cfg_attr` input"));
    let res = (|| -> PResult<'_, _> {
        let pred_start = parser.token.span;
        let meta = MetaItemOrLitParser::parse_single(
            &mut parser,
            ShouldEmit::Nothing,
            AllowExprMetavar::Yes,
        )?;
        let pred_span = pred_start.with_hi(parser.token.span.hi());
        let pred: Result<CfgEntry, ErrorGuaranteed> = AttributeParser::parse_single_args(
            sess,
            item.span,
            item.span,
            AttrStyle::Inner,
            AttrPath {
                segments: item
                    .path
                    .segments
                    .iter()
                    .map(|seg| seg.ident.name)
                    .collect(),
                span: item.path.span,
            },
            None,
            AttributeSafety::Normal,
            ParsedDescription::Attribute,
            pred_span,
            CRATE_NODE_ID,
            AstTarget::None(Target::Crate),
            None,
            ShouldEmit::Nothing,
            &meta,
            rustc_attr_parsing::parse_cfg_entry,
            &CFG_TEMPLATE,
        );
        parser.expect(exp!(Comma))?;
        let mut inner = vec![];
        while parser.token != rustc_ast::token::Eof {
            inner.push(parser.parse_attr_item(ForceCollect::No)?.node);
            if !parser.eat(exp!(Comma)) {
                break;
            }
        }
        Ok((pred, inner))
    })();
    match res {
        Ok((Ok(pred), inner)) if parser.token == rustc_ast::token::Eof => Some((pred, inner)),
        Ok(_) => None,
        Err(diag) => {
            diag.cancel();
            None
        }
    }
}
