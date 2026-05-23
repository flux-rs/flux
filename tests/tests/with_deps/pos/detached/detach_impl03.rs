#![allow(unused)]

extern crate flux_core;

use flux_rs::{assert, attrs::*};

pub mod wrapper {

    #[flux_rs::reflect]
    #[derive(PartialEq)]
    pub enum Role {
        User,
        Admin,
    }

    #[flux_rs::specs {

        impl std::cmp::PartialEq for Role {
            #[reft] fn is_eq(self: Role, other: Role, res: bool) -> bool {
                res <=> (self == other)
            }
            #[reft] fn is_ne(self: Role, other: Role, res: bool) -> bool {
                res <=> (self != other)
            }
            fn eq(&Role[@r1], other: &Role[@r2]) -> bool[r1 == r2];
        }

    }]
    const _: () = ();
}

fn test() {
    use wrapper::Role;
    let r1 = Role::User;
    let r2 = Role::User;
    let r3 = Role::Admin;
    assert(r1 == r2); // checks
    assert(r1 == r1); // checks
    assert(r1 != r3); // checks
}

// --------------------------------------------------------------------------------------
