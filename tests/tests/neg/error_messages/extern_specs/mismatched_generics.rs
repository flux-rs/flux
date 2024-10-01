//@aux-build:mismatched_generics_aux.rs

extern crate mismatched_generics_aux;

use flux_rs::*;
use mismatched_generics_aux::S;

#[extern_spec]
struct S<T>; //~ERROR invalid extern spec for struct

// The parameter should be called A
#[extern_spec(std::ops)]
impl<T> Iterator for Range<T> {} //~ERROR invalid extern spec for implementation
