//@aux-build:dup_extern_spec_aux.rs

extern crate dup_extern_spec_aux;

use dup_extern_spec_aux::test01;
use flux_rs::*;

#[extern_spec]
fn test01();

#[extern_spec]
fn test01(); //~ERROR multiple extern specs
