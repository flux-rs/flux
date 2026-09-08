(set-logic HORN)

;; Tag 0: Ret at 55:5: 55:10 (ESpan { span: tests/pos/surface/test01.rs:44:32: 44:37 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k8
(declare-fun k0 (Int Bool) Bool)
;; orig: $k4
(declare-fun k1 (Bool) Bool)
;; orig: $k5
(declare-fun k2 (Int Bool) Bool)
;; orig: $k6
(declare-fun k3 (Int Bool) Bool)
;; orig: $k7
(declare-fun k4 (Int Bool) Bool)
;; orig: $k9
(declare-fun k5 (Int Bool Int Int) Bool)
;; orig: $k0
(declare-fun k6 (Bool) Bool)
;; orig: $k1
(declare-fun k7 (Int Bool) Bool)
;; orig: $k2
(declare-fun k8 (Int Bool) Bool)
;; orig: $k3
(declare-fun k9 (Int Bool) Bool)

(assert (forall ((a0 Bool)) (=> true (k0 1 a0))))
(assert (forall ((a0 Bool)) (=> true (k1 a0))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)) (=> (k0 a1 a0) (k2 a1 a0))))
(assert (forall ((a0 Bool)) (=> true (k3 2 a0))))
(assert (forall ((a0 Bool)(a2 Int)(_$ Int)) (=> (k0 a2 a0) (k4 a2 a0))))
(assert (forall ((a0 Bool)(a3 Int)(_$ Int)) (=> (k4 a3 a0) (k0 a3 a0))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k1 a0) (not a0) (k2 a4 a0) (k3 a5 a0) (not (> (+ a4 a5) 0))) false)))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true)) (k5 a7 true a6 a7))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true)) (k6 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true)) (k7 a6 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)(a8 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true) (k5 a8 true a6 a7)) (k8 a8 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)(a9 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true) (k5 a9 true a6 a7)) (k9 a9 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)(a10 Int)(_$ Int)) (=> (and (k1 a0) a0 (k2 a6 true) (k3 a7 true) (k9 a10 true)) (k5 a10 true a6 a7))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)) (=> (and (k1 a0) a0 (k6 true) (k9 a11 true)) (k9 (+ a11 1) true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(a12 Int)(_$ Int)) (=> (and (k1 a0) a0 (k6 true) (k9 a11 true) (k7 a12 true)) (k2 a12 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(a13 Int)(_$ Int)) (=> (and (k1 a0) a0 (k6 true) (k9 a11 true) (k8 a13 true)) (k3 a13 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(a14 Int)(_$ Int)) (=> (and (k1 a0) a0 (k6 true) (k9 a11 true) (k9 a14 true)) (k4 a14 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(a15 Int)(_$ Int)) (=> (and (k1 a0) a0 (k6 true) (k9 a11 true) (k4 a15 true)) (k9 a15 true))))

(check-sat)
