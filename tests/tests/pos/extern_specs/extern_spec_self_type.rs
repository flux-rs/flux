//@aux-build:extern_spec_self_type_aux.rs

extern crate extern_spec_self_type_aux;

use flux_rs::attrs::*;

#[extern_spec(extern_spec_self_type_aux)]
#[refined_by(x: int)]
struct MyStruct;

#[extern_spec(extern_spec_self_type_aux)]
impl MyStruct {
    #[sig(fn(&Self[@x]) -> i32[x])]
    fn get_x(&self) -> i32;
}
