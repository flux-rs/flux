#![no_std]
#![cfg_attr(doc, deny(rustdoc::broken_intra_doc_links))]
#![cfg_attr(flux, feature(step_trait))]
#![cfg_attr(flux, feature(sized_hierarchy))]
#![cfg_attr(flux, feature(try_trait_v2))]
#![cfg_attr(flux, flux::no_suggestions)]

pub mod iter;
pub mod ops;

#[cfg(any(flux, doc))]
pub mod mem;

#[cfg(any(flux, doc))]
pub mod option;

#[cfg(any(flux, doc))]
pub mod result;

#[cfg(any(flux, doc))]
pub mod cmp;

#[cfg(any(flux, doc))]
pub mod clone;

#[cfg(any(flux, doc))]
pub mod slice;

#[cfg(any(flux, doc))]
pub mod array;

#[cfg(any(flux, doc))]
pub mod num;

#[cfg(any(flux, doc))]
pub mod ptr;

#[cfg(any(flux, doc))]
pub mod convert;

#[cfg(any(flux, doc))]
pub mod alloc;

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
