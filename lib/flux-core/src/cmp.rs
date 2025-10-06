use core::marker::PointeeSized;

use flux_attrs::*;

defs! {
    fn uif_eq<A, B>(a: A, b: B) -> bool;
}

#[extern_spec]
#[assoc(
    fn eq(x: Self, y: Rhs) -> bool { uif_eq(x, y) }
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[Self::eq(s, t)] )]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool[!Self::eq(s, t)] )]
    fn ne(&self, other: &Rhs) -> bool;
}

#[macro_export]
macro_rules! eq {
    ($type_name:ident) => {
        #[specs {
            impl PartialEq for $type_name {
                #[reft] fn eq(self: $type_name, other: $type_name) -> bool {
                        self == other
                }
                fn eq(&$type_name[@v1], other: &$type_name[@v2]) -> bool[<$type_name as PartialEq>::eq(v1, v2)];
            }
        }]
        const _: () = ();
    };
}
