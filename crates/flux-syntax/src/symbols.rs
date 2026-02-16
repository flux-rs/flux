use flux_macros::symbols;
use rustc_span::{Symbol, edition::Edition};

symbols! {
    Keywords {
        Bitvec: "bitvec",
        Exists: "exists",
        Forall: "forall",
        Hrn: "hrn",
        Hdl: "hdl",
        Requires: "requires",
        Ensures: "ensures",
        Property: "property",
        Qualifier: "qualifier",
        Sort: "sort",
        Strg: "strg",
        Trusted: "trusted",
        Reft: "reft",
        Invariant: "invariant",
        RefinedBy: "refined_by",
    }

    Symbols {
        Map,
        Set,
        int,
        no_panic,
        no_panic_if,
        ptr_size,
        real,
    }
}

/// All Rust keywords plus extra Flux keywords.
pub mod kw {
    #![allow(non_upper_case_globals)]

    use rustc_span::Symbol;
    pub use rustc_span::symbol::kw::*;

    pub use super::kw_generated::*;

    // Predefined symbols in rustc that are not Rust keywords but are Flux keywords.
    // Update this in tandem with `is_flux_reserved`
    pub const Opaque: Symbol = rustc_span::symbol::sym::opaque;
    pub const Local: Symbol = rustc_span::symbol::sym::local;
}

pub mod sym {
    pub use rustc_span::sym::*;

    pub use super::sym_generated::*;
}

pub fn is_reserved(sym: Symbol, edition: Edition) -> bool {
    // FIXME: We should treat these as reserved and adjust the parser to be consistent with Rust.
    if sym == kw::SelfLower || sym == kw::SelfUpper || sym == kw::Crate || sym == kw::Super {
        return false;
    }
    sym.is_reserved(|| edition) || is_flux_reserved(sym)
}

// Update in tandem with predefined non-keyword symbols in `kw`
fn is_flux_reserved(sym: Symbol) -> bool {
    (kw::Bitvec <= sym && sym <= kw::Strg) || sym == kw::Opaque || sym == kw::Local
}
