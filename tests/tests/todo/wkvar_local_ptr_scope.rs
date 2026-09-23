// Run with `cargo x --suggestions run tests/tests/todo/wkvar_local_ptr_scope.rs`.
#[path = "../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[derive(Clone, Copy)]
enum SubscriptionInner {
    Clock,
    Fd,
}

#[derive(Clone, Copy)]
struct Subscription {
    userdata: u64,
    subscription_inner: SubscriptionInner,
}

#[flux::trusted]
#[flux::sig(fn() -> Result<Subscription, ()>)]
fn read_subscription() -> Result<Subscription, ()> {
    Err(())
}

pub fn poll_parse_clock(timeouts: &mut RVec<(u64, u64)>, userdata: u64) -> Result<(), ()> {
    timeouts.push((userdata, userdata));
    Ok(())
}

fn poll_parse_fds() -> Result<(), ()> {
    Ok(())
}

#[flux::sig(fn(tos: &strg RVec<(u64, u64)>[@timeouts_old]) -> Result<(), ()>
    ensures tos: RVec<(u64, u64)>[#timeouts_new]
)]
pub fn parse_subscriptions(timeouts: &mut RVec<(u64, u64)>) -> Result<(), ()> {
    let subscription = read_subscription()?;
    match subscription.subscription_inner {
        SubscriptionInner::Clock => {
            poll_parse_clock(timeouts, subscription.userdata)?;
        }
        SubscriptionInner::Fd => poll_parse_fds()?,
    }
    Ok(())
}
