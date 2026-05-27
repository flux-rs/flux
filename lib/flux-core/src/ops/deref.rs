use flux_attrs::*;

// #[extern_spec(core::ops)]
// #[assoc(fn as_deref(v: Self, target: Self::Target) -> bool { true })]
// trait Deref {
//     // #[sig(fn(self: &Self[@v]) -> &Self::Target{target: <Self as Deref>::as_deref(v, target)})]
//     // #[sig(fn(self: &Self[@v]) -> &Self::Target)]
//     fn deref(&self) -> &Self::Target;
// }

#[extern_spec(core::ops)]
#[assoc(fn as_deref(v: Self, target: Self::Target) -> bool { true })]
trait Deref {
    #[sig(fn(self: &Self[@v]) -> &Self::Target{target: Self::as_deref(v, target)})]
    fn deref(&self) -> &Self::Target;
}
