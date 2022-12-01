//! Expanding the expression alias `defn` in [`flux_middle::fhir`]
//! i.e. replacing {v:nat(v)} with {v:0<=v} in all the relevant signatures.
//! As this is done _after_ wf-checking, there should be no user-visible errors during expansion...

use flux_middle::fhir;

pub fn expand_fhir_map(map: fhir::Map) -> fhir::Map {
    panic!("OH NO!")
}
