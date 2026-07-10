use flux_rs::{assert, attrs::*};
extern crate flux_core;

#[reflect]
#[derive(PartialEq, Eq)]
pub enum State {
    On,
    Off,
}
flux_core::eq!(State);

pub fn test_eq() {
    let s1 = State::On;
    let s2 = State::On;
    let s3 = State::Off;
    assert(s1 == s2); // checks
    assert(s1 == s1); // checks
    assert(s1 != s3); // checks
}
