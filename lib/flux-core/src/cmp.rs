use core::marker::PointeeSized;

use flux_attrs::*;

#[extern_spec]
#[assoc(
    fn is_eq(x: Self, y: Rhs, res: bool) -> bool { true }
    fn is_ne(x: Self, y: Rhs, res: bool) -> bool { true }
)]
trait PartialEq<Rhs: PointeeSized = Self>: PointeeSized {
    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_eq(s, t, v)})]
    fn eq(&self, other: &Rhs) -> bool;

    #[spec(fn(&Self[@s], &Rhs[@t]) -> bool{v: Self::is_ne(s, t, v)})]
    fn ne(&self, other: &Rhs) -> bool;
}

#[macro_export]
macro_rules! eq {
    ($type_name:ident) => {
        #[specs {
                    impl PartialEq for $type_name {
                        #[reft] fn is_eq(self: $type_name, other: $type_name, res: bool) -> bool {
                            res <=> (self == other)
                        }
                        #[reft] fn is_ne(self: $type_name, other: $type_name, res: bool) -> bool {
                            res <=> (self != other)
                        }
                        fn eq(&$type_name[@v1], other: &$type_name[@v2]) -> bool[v1 == v2];
                    }
                }]
        const _: () = ();
    };
}
