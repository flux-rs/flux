(set-logic HORN)

;; Tag 0: NoPanic(DefId(2:4252 ~ core[9471]::ops::function::FnOnce::call_once), MightPanic(NotInCallGraph)) at 7:5: 7:10
;; Tag 1: Ret at 8:1: 8:2 (ESpan { span: tests/pos/surface/closure09_exi.rs:1:33: 1:39 (#0), base: None })

(declare-type-var T0)
;; alias reft: <({b0. F[b0] | $k0(b0) }) as FnOnce<({b1. i32[b1] | $k1(b1) },)>>::no_panic
(declare-const c0 Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)
;; orig: $k3
(declare-fun k2 (Int Int) Bool)

(assert (forall ((a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a1 a0) (k1 a2 a0) (k0 a3 a0) (k1 a4 a0) (< a4 a5)) (k2 a5 a0))))
(assert (forall ((a0 Int)) (=> (not (=> false (or c0 false))) false)))
(assert (forall ((a0 Int)) (=> true (k0 a0 a0))))
(assert (forall ((a0 Int)) (=> true (k1 99 a0))))
(assert (forall ((a0 Int)(a6 Int)(_$ Int)) (=> (and (k2 a6 a0) (not (< 99 a6))) false)))

(check-sat)
