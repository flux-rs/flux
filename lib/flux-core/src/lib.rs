#![no_std]
#![cfg_attr(flux, feature(step_trait))]
#![cfg_attr(flux, feature(sized_hierarchy))]

mod iter;
mod ops;

#[cfg(flux)]
mod mem;

#[cfg(flux)]
mod option;

#[cfg(flux)]
mod cmp;

#[cfg(flux)]
mod clone;

#[cfg(flux)]
mod slice;

#[cfg(flux)]
mod num;

#[cfg(flux)]
mod convert;

// -------------------------------------------------------------------

#[macro_export]
macro_rules! eq {
    ($(#[trusted])? $type:ty) => {
        $crate::eq!(@impl #[trusted] $type);
    };
    ($type:ty) => {
        $crate::eq!(@impl $type);
    };
    (@impl $(#[$attr:meta])* $type_name:ty) => {
        #[cfg_attr(
            flux,
            flux::specs {
                $(#[$attr])*
                impl std::cmp::PartialEq for $type_name {
                    #[reft] fn is_eq(self: $type_name, other: $type_name, res: bool) -> bool {
                        res <=> (self == other)
                    }
                    #[reft] fn is_ne(self: $type_name, other: $type_name, res: bool) -> bool {
                        res <=> (self != other)
                    }
                    fn eq(&$type_name[@v1], other: &$type_name[@v2]) -> bool[v1 == v2];
                }
            }
        )]
        const _: () = ();
    };
}
