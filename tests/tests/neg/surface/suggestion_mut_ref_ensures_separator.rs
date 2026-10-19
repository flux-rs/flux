// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: ensures tos: crate::rvec::RVec<u8>[{ len: old_tos.len + 1 }], pfds: crate::rvec::RVec<u8>[{ len: old_pfds.len + 1 }]
// Reprinting two strong-reference postconditions must separate them with a comma.
#[path = "../../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

#[flux::trusted]
#[flux::sig(fn(&RVec<u8>{n: n > 10}))]
fn needs_long(_: &RVec<u8>) {}

#[flux::sig(fn(
    tos: &strg RVec<u8>[@old_tos],
    pfds: &strg RVec<u8>[@old_pfds]
    ) -> ()
    ensures tos: RVec<u8>[old_tos.len + 1], pfds: RVec<u8>[old_pfds.len + 1]
)]
fn parse_subscriptions(tos: &mut RVec<u8>, pfds: &mut RVec<u8>) {
    tos.push(0);
    pfds.push(0);
    needs_long(tos); //~ ERROR refinement type error
    needs_long(pfds); //~ ERROR refinement type error
}
