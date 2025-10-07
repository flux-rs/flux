#![allow(unused)]

extern crate flux_core;

use flux_rs::{assert, attrs::*};

pub mod wrapper {

    use flux_rs::specs;

    #[flux_rs::reflect]
    #[derive(PartialEq)]
    pub enum Role {
        User,
        Admin,
    }
    flux_core::eq!(Role);
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
