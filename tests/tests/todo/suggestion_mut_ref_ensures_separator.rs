// compile-flags: -Fsuggestions-z3=process -Ffix-suggestions
// Run with `cargo x --suggestions run tests/tests/todo/suggestion_mut_ref_ensures_separator.rs -- -Fsuggestions-z3=process -Ffix-suggestions`.
#[path = "../lib/rvec.rs"]
mod rvec;

use rvec::RVec;

#[flux::trusted]
#[flux::sig(fn(&RVec<u8>{n: n > 10}))]
fn needs_long(_: &RVec<u8>) {}

#[flux::sig(fn(
    tos: &strg RVec<u8>[@old_tos],
    pfds: &strg RVec<u8>[@old_pfds]
    ) -> ()
    ensures tos: RVec<u8>[old_tos], pfds: RVec<u8>[old_pfds]
)]
fn parse_subscriptions(tos: &mut RVec<u8>, pfds: &mut RVec<u8>) {
    tos.push(0);
    pfds.push(0);
    needs_long(tos);
    needs_long(pfds);
}
