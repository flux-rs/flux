(set-logic HORN)

;; Tag 0: NoPanic(DefId(2:4248 ~ core[9471]::ops::function::FnMut::call_mut), MightPanic(NotInCallGraph)) at 75:20: 75:24
;; Tag 1: Ret at 76:1: 76:2 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:69:36: 69:37 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
;; alias reft: <({b0. F[b0] | $k4(b0) }) as FnOnce<({b1. usize[b1] | $k5(b1) },)>>::no_panic
(declare-const c0 Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k2
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k4
(declare-fun k2 (Int Int Int Int) Bool)
;; orig: $k7
(declare-fun k3 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)) (=> (>= reftgen$n$0 0) (k0 a0 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k1 a1 reftgen$n$0 a0) (>= a1 0) (not (=> false (or c0 false)))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k1 a1 reftgen$n$0 a0) (>= a1 0) (k0 a2 reftgen$n$0 a0)) (k2 a2 reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k1 a1 reftgen$n$0 a0) (>= a1 0) (k2 a3 reftgen$n$0 a0 a1)) (k0 a3 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a4 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 a4) (< a4 reftgen$n$0)) (k1 a4 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a5 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a5 reftgen$n$0 a0)) (k3 a5 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a6 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k3 a6 reftgen$n$0 a0)) (k0 a6 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a7 Int)) (=> (>= reftgen$n$0 0) (k3 a7 reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a8 Adt0)(_$ Int)(_$ Int)(a9 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= (fld0$0 a8) (- reftgen$n$0 0)) (<= 0 (fld0$0 a8)) (k0 a9 reftgen$n$0 a0) (not (= (fld0$0 a8) reftgen$n$0))) false)))

(check-sat)
