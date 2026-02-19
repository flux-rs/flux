// This file produces a mir with a basic block of the form
//
// ```
//  bb1: {
//      unblock((*_1).0);
//      StorageDead(_2);
//      fold(*_1);
//      return;
//  }
// ```
//
// We consider this an *exit basic block* because the only relevant statement is a return and we
// treat it specially. However we must be sure we execute all ghost statements.

use flux_rs::attrs::*;

struct S {
    f: usize,
}

impl S {
    #[spec(fn(l: &mut S) ensures l: S)]
    fn test(&mut self) {
        takes_closure(|| {
            self.f = 0;
        }) // the missing semicolon is important to generate the desired mir
    }
}

pub fn takes_closure(f: impl FnMut()) {}
