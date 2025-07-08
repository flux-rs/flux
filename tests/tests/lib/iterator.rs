#![allow(unused)]
#![feature(step_trait)]

use std::{
    iter::{Enumerate, Skip, Step, Zip},
    ops::Range,
    slice::Iter,
};
extern crate flux_core;

#[path = "iter.rs"]
mod iter;
