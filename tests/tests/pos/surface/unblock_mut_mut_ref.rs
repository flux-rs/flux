use flux_rs::*;

fn test00<T>(x: T, f: impl FnOnce(&mut T)) {}

fn test01(x: &mut i32) {
    // The type of `x` inside the closure is `&mut ∃v:(). (&mut i32)[v]`. We are testing that the
    // unblock statement we geneunblocking for `**xx` works appropriately
    test00(x, |x| {
        let r = &mut **x;
    });
}
