use flux_macros::symbols;

symbols! {
    Keywords {
        Requires: "requires",
        Ensures: "ensures",
        Strg: "strg",
        Qualifier: "qualifier",
        Property: "property",
        Sort: "sort",
        Bitvec: "bitvec",
        Hrn: "hrn",
        Hdl: "hdl",
        Forall: "forall",
        Exists: "exists",
    }
}

/// Module exporting all predefined Rust keywords plus extra Flux keywords.
pub mod kw {
    #![allow(non_upper_case_globals)]

    use rustc_span::Symbol;
    pub use rustc_span::symbol::kw::*;

    pub use super::kw_generated::*;

    pub const Opaque: Symbol = rustc_span::symbol::sym::opaque;
    pub const Local: Symbol = rustc_span::symbol::sym::local;
}
