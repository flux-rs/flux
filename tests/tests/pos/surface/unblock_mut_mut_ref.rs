use flux_rs::*;

mod bob {
    // TODO(auto-strong) fn test00<T>(x: T) {}
    fn test00<T>(x: &mut T) {}

    #[flux::sig(fn(x: &mut i32) ensures x: i32)]
    fn test01_simple(x: &mut i32) {
        test00(x);
    }
}

mod poly {

    // TODO(auto-strong) fn test00<T>(x: T, f: impl FnOnce(&mut T)) {}
    fn test00<T>(x: &mut T, f: impl FnOnce(&mut &mut T)) {}

    #[flux::sig(fn(x: &mut i32) ensures x: i32)]
    fn test01(x: &mut i32) {
        // The type of `x` inside the closure is `&mut ∃v:(). (&mut i32)[v]`. We are testing that the
        // unblock statement we geneunblocking for `**xx` works appropriately
        test00(x, |y| {
            let r = &mut **y;
        });
    }
}
