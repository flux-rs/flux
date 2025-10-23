#[path = "../../lib/svec.rs"]
mod svec;
use svec::{SVec};

#[flux::trusted]
#[flux::sig(fn(bool[@b]) requires b)]
fn assert(_b: bool) {}

#[flux::sig(fn() -> SVec[iseq_empty()])]
pub fn test00() -> SVec {
    SVec::new()
}


#[flux::proven_externally]
#[flux::sig(fn(&SVec[@elems], i32[@v]) ensures iseq_pop(iseq_push(elems, v)) == v)]
fn push_pop_eq(_vec: &SVec, _elem: i32) {}

#[flux::sig(fn() -> i32[2])]
pub fn test01() -> i32 {
    let mut vec = SVec::new();
    vec.push(1);
    push_pop_eq(&vec, 2);
    vec.push(2);
    vec.pop()
}

#[flux::proven_externally]
#[flux::sig(fn(&SVec[@elems], i32[@v]) ensures iseq_get(iseq_push(elems, v), iseq_len(elems)) == v)]
fn get_len_push_eq(_vec: &SVec, _elem: i32) {}

#[flux::proven_externally]
#[flux::sig(fn(&SVec[@elems], i32[@v]) ensures iseq_len(iseq_push(elems, v)) == iseq_len(elems) + 1)]
fn push_len_eq_plus_one(_vec: &SVec, _elem: i32) {}

#[flux::proven_externally]
#[flux::sig(fn(&SVec[@elems], i32[@v], i32[@i]) requires 0 <= i && i < iseq_len(elems) ensures iseq_get(iseq_push(elems, v), i) == iseq_get(elems, i))]
fn push_get_unchanged(_elems: &SVec, _elem: i32, _idx: i32) {}

pub fn test02() {
    let mut vec = SVec::new();
    push_len_eq_plus_one(&vec, 1);
    get_len_push_eq(&vec, 1);
    vec.push(1);
    push_len_eq_plus_one(&vec, 2);
    get_len_push_eq(&vec, 2);
    push_get_unchanged(&vec, 2, 0);
    vec.push(2);
    push_len_eq_plus_one(&vec, 2);
    get_len_push_eq(&vec, 3);
    push_get_unchanged(&vec, 3, 0);
    push_get_unchanged(&vec, 3, 1);
    vec.push(3);
    assert(*vec.get(0) == 1);
    assert(*vec.get(1) == 2);
    assert(*vec.get(2) == 3);
}
