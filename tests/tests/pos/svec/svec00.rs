#[path = "../../lib/svec.rs"]
mod svec;
use svec::{SVec};

#[flux::trusted]
#[flux::sig(fn(bool[@b]) requires b)]
fn assert(_b: bool) {}

#[flux::sig(fn() -> SVec<T>[vseq_empty()])]
pub fn test00<T>() -> SVec<T> {
    SVec::new()
}

#[flux::proven_externally]
#[flux::sig(fn(&SVec<T>[@elems]) requires elems == vseq_empty() ensures vseq_len(elems) == 0)]
fn empty_len<T>(_vec: &SVec<T>) {}

#[flux::proven_externally]
#[flux::sig(fn(&SVec<i32>[@elems], i32[@v]) ensures iseq_pop(iseq_push(elems, v)) == v)]
fn push_pop_eq(_vec: &SVec<i32>, _elem: i32) {}

#[flux::proven_externally]
#[flux::sig(fn(&SVec<i32>[@elems], i32[@v]) ensures vseq_len(iseq_push(elems, v)) == vseq_len(elems) + 1)]
fn push_len_eq_plus_one(_vec: &SVec<i32>, _elem: i32) {}

#[flux::sig(fn() -> i32[2])]
pub fn test01() -> i32 {
    let mut vec = SVec::new();
    empty_len(&vec);
    push_len_eq_plus_one(&vec, 1);
    vec.push(1);
    push_len_eq_plus_one(&vec, 2);
    push_pop_eq(&vec, 2);
    vec.push(2);
    vec.pop()
}

#[flux::proven_externally]
#[flux::sig(fn(&SVec<i32>[@elems], i32[@v]) ensures vseq_get(iseq_push(elems, v), vseq_len(elems)) == v)]
fn get_len_push_eq(_vec: &SVec<i32>, _elem: i32) {}

#[flux::proven_externally]
#[flux::sig(fn(&SVec<i32>[@elems], i32[@v], i32[@i]) requires 0 <= i && i < vseq_len(elems) ensures vseq_get(iseq_push(elems, v), i) == vseq_get(elems, i))]
fn push_get_unchanged(_elems: &SVec<i32>, _elem: i32, _idx: i32) {}

pub fn test02() {
    let mut vec = SVec::new();
    empty_len(&vec);
    push_len_eq_plus_one(&vec, 1);
    get_len_push_eq(&vec, 1);
    vec.push(1);
    push_len_eq_plus_one(&vec, 2);
    get_len_push_eq(&vec, 2);
    push_get_unchanged(&vec, 2, 0);
    vec.push(2);
    push_len_eq_plus_one(&vec, 3);
    get_len_push_eq(&vec, 3);
    push_get_unchanged(&vec, 3, 0);
    push_get_unchanged(&vec, 3, 1);
    vec.push(3);
    assert(*vec.get(0) == 1);
    assert(*vec.get(1) == 2);
    assert(*vec.get(2) == 3);
}
