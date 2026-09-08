(set-logic HORN)

;; Tag 0: Predicate at 8:5: 8:12 (ESpan { span: tests/pos/surface/closure06.rs:2:35: 2:41 (#0), base: None })
;; Tag 1: Predicate at 8:5: 8:12 (ESpan { span: tests/pos/surface/closure06.rs:2:35: 2:41 (#0), base: None })
;; Tag 2: NoPanic(DefId(2:4252 ~ core[9471]::ops::function::FnOnce::call_once), MightPanic(NotInCallGraph)) at 8:5: 8:12
;; Tag 3: Ret at 9:1: 9:2 (ESpan { span: tests/pos/surface/closure06.rs:1:42: 1:46 (#0), base: None })

(declare-type-var T0)
;; alias reft: <({b0. F[b0] | $k0(b0) }) as FnOnce<({b1. i32[b1] | $k1(b1) },)>>::no_panic
(declare-const c0 Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k3
(declare-fun k2 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (not (<= reftgen$n$0 a2))) false)))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (k0 a3 reftgen$n$0 a0) (k1 a4 reftgen$n$0 a0) (not (<= reftgen$n$0 a4))) false)))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0 a0) (k1 a2 reftgen$n$0 a0) (k0 a3 reftgen$n$0 a0) (k1 a4 reftgen$n$0 a0) (<= reftgen$n$0 a5)) (k2 a5 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)) (=> (not (=> false (or c0 false))) false)))
(assert (forall ((reftgen$n$0 Int)(a0 Int)) (=> true (k0 a0 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)) (=> true (k1 (+ reftgen$n$0 1) reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(a6 Int)(_$ Int)) (=> (and (k2 a6 reftgen$n$0 a0) (not (<= reftgen$n$0 a6))) false)))

(check-sat)
