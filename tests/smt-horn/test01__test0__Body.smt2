(set-logic HORN)

;; Tag 0: Ret at 28:5: 28:11 (ESpan { span: tests/pos/surface/test01.rs:17:56: 17:62 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k4
(declare-fun k0 (Int Int Int Bool) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Bool) Bool)
;; orig: $k1
(declare-fun k2 (Int Int Int Bool) Bool)
;; orig: $k2
(declare-fun k3 (Int Int Int Bool) Bool)
;; orig: $k3
(declare-fun k4 (Int Int Int Bool) Bool)
;; orig: $k5
(declare-fun k5 (Int Int Int Bool) Bool)

(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0)) (k0 reftgen$m$1 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0)) (k1 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0)) (k2 reftgen$n$0 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0) (k0 a1 reftgen$n$0 reftgen$m$1 a0)) (k3 a1 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0) (k0 a2 reftgen$n$0 reftgen$m$1 a0)) (k4 a2 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (not a0) (k4 a3 reftgen$n$0 reftgen$m$1 a0)) (k0 a3 reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0) (k5 reftgen$n$0 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0) (k1 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0 (k5 a4 reftgen$n$0 reftgen$m$1 true)) (k2 a4 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0) (k3 reftgen$m$1 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0 (k5 a5 reftgen$n$0 reftgen$m$1 true)) (k4 a5 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a6 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) a0 (k4 a6 reftgen$n$0 reftgen$m$1 true)) (k5 a6 reftgen$n$0 reftgen$m$1 true))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (k1 reftgen$n$0 reftgen$m$1 a0) (k4 a7 reftgen$n$0 reftgen$m$1 a0)) (k4 (+ a7 1) reftgen$n$0 reftgen$m$1 a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$m$1 Int)(a0 Bool)(_$ Int)(_$ Int)(a7 Int)(_$ Int)(a8 Int)(_$ Int)(a9 Int)(_$ Int)(a10 Int)(_$ Int)) (=> (and (< reftgen$n$0 reftgen$m$1) (k1 reftgen$n$0 reftgen$m$1 a0) (k4 a7 reftgen$n$0 reftgen$m$1 a0) (k4 a8 reftgen$n$0 reftgen$m$1 a0) (k2 a9 reftgen$n$0 reftgen$m$1 a0) (k3 a10 reftgen$n$0 reftgen$m$1 a0) (not (<= 0 (- a8 reftgen$n$0)))) false)))

(check-sat)
