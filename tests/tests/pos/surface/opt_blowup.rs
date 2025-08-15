// extern crate flux_core;
use flux_rs::attrs::*;

/*  These tests motivate the `bot-elim` optimization. Before the optimization,
    `let2` produces the constraint

∀ n: int.
  ∀ a0: int.
    (n < a0) =>
      ∀ a1: int.
        (a0 < a1) =>
          $k3(a1)[n, a0, a1] ~ Call at 25:5: 25:14
          $k4(a0)[n, a0, a1] ~ Fold at 25:5: 25:14
          $k5(a1)[n, a0, a1] ~ Fold at 25:5: 25:14
          ∀ a2: int.
            $k3(a2)[n, a0, a1] => (n < a2) ~ Ret at 25:5: 25:14
      $k7(a0)[n, a0] ~ Fold at 22:45: 22:49
      $k0(a0)[n] ~ Goto(bb9) at 22:45: 22:49
      ∀ a1: int.
        $k6(a1)[n, a0] => $k1(a1)[a0, n] ~ Goto(bb9) at 22:45: 22:49
      ∀ a1: int.
        $k7(a1)[n, a0] => $k2(a1)[a0, n] ~ Goto(bb9) at 22:45: 22:49
  $k0(n)[n] ~ Goto(bb9) at 19:45: 19:49
  ∀ a0: int.
    $k9(a0)[n] => $k1(a0)[n, n] ~ Goto(bb9) at 19:45: 19:49
  ∀ a0: int.
    $k10(a0)[n] => $k2(a0)[n, n] ~ Goto(bb9) at 19:45: 19:49
  ∀ a0: int.
    $k0(a0)[n] =>
      ∀ a1: int.
        $k1(a1)[a0, n] => (n < a1) ~ Ret at 26:2: 26:2

but after the optimization we get the more compact

∀ n: int.
  ∀ a0: int.
    (n < a0) =>
      ∀ a1: int.
        (a0 < a1) =>
          $k3(a1)[n, a0, a1] ~ Call at 25:5: 25:14
          ∀ a2: int.
            $k3(a2)[n, a0, a1] => (n < a2) ~ Ret at 25:5: 25:14

*/

#[spec(fn (k: i32) -> Option<i32{v:k < v}>)]
pub fn burpi(k: i32) -> Option<i32> {
    if k % 2 == 0 { Some(k + 1) } else { None }
}

#[spec(fn (n: i32) -> Option<i32{v:n < v}>)]
pub fn let2(n: i32) -> Option<i32> {
    let mut res = n;

    let Some(v0) = burpi(res) else { return None };
    res = v0;

    let Some(v1) = burpi(res) else { return None };
    res = v1;

    Some(res)
}

#[spec(fn (n: i32) -> Option<i32{v:n < v}>)]
pub fn let3(n: i32) -> Option<i32> {
    let mut res = n;

    let Some(v0) = burpi(res) else { return None };
    res = v0;

    let Some(v1) = burpi(res) else { return None };
    res = v1;

    let Some(v2) = burpi(res) else { return None };
    res = v2;

    Some(res)
}

#[spec(fn (n: i32) -> Option<i32{v:n < v}>)]
pub fn blah2(n: i32) -> Option<i32> {
    let mut res = n;

    let v0 = burpi(res)?;
    res = v0;

    let v1 = burpi(res)?;
    res = v1;

    Some(res)
}

#[spec(fn (n: i32) -> Option<i32{v:n < v}>)]
pub fn blah3(n: i32) -> Option<i32> {
    let mut res = n;

    let v0 = burpi(res)?;
    res = v0;

    let v1 = burpi(res)?;
    res = v1;

    let v2 = burpi(res)?;
    res = v2;

    Some(res)
}

// This should generate a trivial `true` constraint
#[spec(fn (n:usize{false}, m: usize) -> usize{v:v < m})]
fn test_false_pre(n:usize, m:usize) -> usize {
    let mut i = n;
    let mut res = m;
    while 0 < i {
        res += 1;
        i -= 1;
    }
    res
}
