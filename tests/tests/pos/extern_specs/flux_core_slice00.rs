extern crate flux_core;
use flux_rs::assert;

// --- len / is_empty / index ---

pub fn test_index_after_len(xs: &[i32]) {
    if xs.len() > 0 {
        let _x = xs[0];
    }
}

pub fn test_index_after_is_empty(xs: &[i32]) {
    if !xs.is_empty() {
        let _x = xs[0];
    }
}

// --- first ---

pub fn test_first_branch(xs: &[i32]) {
    if xs.len() > 0 {
        assert(xs.first().is_some());
    }
    if xs.is_empty() {
        assert(xs.first().is_none());
    }
}

// --- iter ---

pub fn test_iter_as_slice_len(xs: &[i32]) {
    let it = xs.iter();
    let ys = it.as_slice();
    assert(xs.len() == ys.len());
}

// --- first_mut / last_mut ---

pub fn test_first_mut_empty() {
    let mut w: [i32; 0] = [];
    assert(w.first_mut().is_none());
}

pub fn test_first_mut_nonempty() {
    let mut v = [1, 2, 3];
    assert(v.first_mut().is_some());
}

pub fn test_first_mut_branch(xs: &mut [i32]) {
    if xs.is_empty() {
        assert(xs.first_mut().is_none());
    } else {
        assert(xs.first_mut().is_some());
    }
}

pub fn test_last_mut_branch(xs: &mut [i32]) {
    if xs.is_empty() {
        assert(xs.last_mut().is_none());
    } else {
        assert(xs.last_mut().is_some());
    }
}

// --- last ---

pub fn test_last_concrete() {
    let v = [10, 40, 30];
    assert(v.last().is_some());
}

pub fn test_last_empty() {
    let w: &[i32] = &[];
    assert(w.last().is_none());
}

pub fn test_last_branch(xs: &[i32]) {
    if xs.is_empty() {
        assert(xs.last().is_none());
    } else {
        assert(xs.last().is_some());
    }
}

// --- get ---

pub fn test_get_in_bounds(xs: &[i32], i: usize) {
    if i < xs.len() {
        assert(xs.get(i).is_some());
    }
}

pub fn test_get_out_of_bounds(xs: &[i32], i: usize) {
    if i >= xs.len() {
        assert(xs.get(i).is_none());
    }
}

pub fn test_get_concrete() {
    let v = [10, 40, 30];
    assert(v.get(0).is_some());
    assert(v.get(2).is_some());
    assert(v.get(3).is_none());
}

// --- split_first ---

pub fn test_split_first_empty() {
    let w: &[i32] = &[];
    assert(w.split_first().is_none());
}

pub fn test_split_first_nonempty() {
    let v = [1, 2, 3];
    assert(v.split_first().is_some());
}

pub fn test_split_first_branch(xs: &[i32]) {
    if xs.is_empty() {
        assert(xs.split_first().is_none());
    } else {
        assert(xs.split_first().is_some());
    }
}

pub fn test_split_first_tail_len(xs: &[i32]) {
    let n = xs.len();
    if let Some((_, tail)) = xs.split_first() {
        assert(tail.len() == n - 1);
    }
}

// --- split_last ---

pub fn test_split_last_empty() {
    let w: &[i32] = &[];
    assert(w.split_last().is_none());
}

pub fn test_split_last_nonempty() {
    let v = [1, 2, 3];
    assert(v.split_last().is_some());
}

pub fn test_split_last_branch(xs: &[i32]) {
    if xs.is_empty() {
        assert(xs.split_last().is_none());
    } else {
        assert(xs.split_last().is_some());
    }
}

pub fn test_split_last_init_len(xs: &[i32]) {
    let n = xs.len();
    if let Some((_, init)) = xs.split_last() {
        assert(init.len() == n - 1);
    }
}

// --- get_mut ---

pub fn test_get_mut_in_bounds(xs: &mut [i32], i: usize) {
    if i < xs.len() {
        assert(xs.get_mut(i).is_some());
    }
}

pub fn test_get_mut_out_of_bounds(xs: &mut [i32], i: usize) {
    if i >= xs.len() {
        assert(xs.get_mut(i).is_none());
    }
}

// --- split_at_mut ---

pub fn test_split_at_mut_lengths(xs: &mut [i32], mid: usize) {
    let n = xs.len();
    if mid <= n {
        let (left, right) = xs.split_at_mut(mid);
        assert(left.len() == mid);
        assert(right.len() == n - mid);
    }
}

// --- split_at_mut_checked ---

pub fn test_split_at_mut_checked_in_bounds(xs: &mut [i32], mid: usize) {
    if mid <= xs.len() {
        assert(xs.split_at_mut_checked(mid).is_some());
    }
}

pub fn test_split_at_mut_checked_lengths(xs: &mut [i32], mid: usize) {
    let n = xs.len();
    if let Some((left, right)) = xs.split_at_mut_checked(mid) {
        assert(left.len() == mid);
        assert(right.len() == n - mid);
    }
}

// --- split_at_checked ---

pub fn test_split_at_checked_in_bounds(xs: &[i32], mid: usize) {
    if mid <= xs.len() {
        assert(xs.split_at_checked(mid).is_some());
    }
}

pub fn test_split_at_checked_out_of_bounds(xs: &[i32], mid: usize) {
    if mid > xs.len() {
        assert(xs.split_at_checked(mid).is_none());
    }
}

pub fn test_split_at_checked_lengths(xs: &[i32], mid: usize) {
    let n = xs.len();
    if let Some((left, right)) = xs.split_at_checked(mid) {
        assert(left.len() == mid);
        assert(right.len() == n - mid);
    }
}
