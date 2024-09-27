//@aux-build:mismatched_generics_aux.rs

extern crate mismatched_generics_aux;

use flux_rs::*;
use mismatched_generics_aux::S;

#[extern_spec]
struct S<T>; //~ERROR aasdf
