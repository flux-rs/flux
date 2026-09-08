(set-logic HORN)

;; Tag 0: Ret at 41:5: 41:10 (ESpan { span: tests/pos/surface/test01.rs:30:32: 30:37 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k4
(declare-fun k0 (Int Bool) Bool)
;; orig: $k0
(declare-fun k1 (Bool) Bool)
;; orig: $k1
(declare-fun k2 (Int Bool) Bool)
;; orig: $k2
(declare-fun k3 (Int Bool) Bool)
;; orig: $k3
(declare-fun k4 (Int Bool) Bool)
;; orig: $k5
(declare-fun k5 (Int Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 1 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k1 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k2 1 a0))))
(assert (forall ((a0 Bool)(_$ Int)(a1 Int)(_$ Int)) (=> (and (not a0) (k0 a1 a0)) (k3 a1 a0))))
(assert (forall ((a0 Bool)(_$ Int)(a2 Int)(_$ Int)) (=> (and (not a0) (k0 a2 a0)) (k4 a2 a0))))
(assert (forall ((a0 Bool)(_$ Int)(a3 Int)(_$ Int)) (=> (and (not a0) (k4 a3 a0)) (k0 a3 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k5 1 true))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k1 true))))
(assert (forall ((a0 Bool)(_$ Int)(a4 Int)(_$ Int)) (=> (and a0 (k5 a4 true)) (k2 a4 true))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k3 1 true))))
(assert (forall ((a0 Bool)(_$ Int)(a5 Int)(_$ Int)) (=> (and a0 (k5 a5 true)) (k4 a5 true))))
(assert (forall ((a0 Bool)(_$ Int)(a6 Int)(_$ Int)) (=> (and a0 (k4 a6 true)) (k5 a6 true))))
(assert (forall ((a0 Bool)(_$ Int)(a7 Int)(_$ Int)) (=> (and (k1 a0) (k4 a7 a0)) (k4 (+ a7 1) a0))))
(assert (forall ((a0 Bool)(_$ Int)(a7 Int)(_$ Int)(a8 Int)(_$ Int)(a9 Int)(_$ Int)) (=> (and (k1 a0) (k4 a7 a0) (k2 a8 a0) (k3 a9 a0) (not (> (+ a8 a9) 0))) false)))

(check-sat)
