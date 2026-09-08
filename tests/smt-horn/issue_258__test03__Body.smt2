(set-logic HORN)

;; Tag 0: Ret at 22:5: 22:42 (ESpan { span: tests/pos/surface/issue-258.rs:20:36: 20:41 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k2
(declare-fun k1 (Int) Bool)
;; orig: $k1
(declare-fun k2 (Int) Bool)
;; orig: $k5
(declare-fun k3 (Int) Bool)
;; orig: $k4
(declare-fun k4 (Int) Bool)
;; orig: $k3
(declare-fun k5 (Int) Bool)
;; orig: $k9
(declare-fun k6 (Int) Bool)
;; orig: $k8
(declare-fun k7 (Int) Bool)
;; orig: $k7
(declare-fun k8 (Int) Bool)
;; orig: $k6
(declare-fun k9 (Int) Bool)

(assert (=> true (k0 1)))
(assert (forall ((a0 Int)) (=> (= a0 0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (k0 a1) (k2 a1))))
(assert (forall ((a2 Int)) (=> (= a2 0) (k3 a2))))
(assert (forall ((a3 Int)(_$ Int)(a4 Int)) (=> (and (= a3 0) (k1 a3) (= a4 0)) (k4 a4))))
(assert (forall ((a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= a3 0) (k1 a3) (k2 a5)) (k5 a5))))
(assert (forall ((a6 Int)) (=> (= a6 0) (k6 a6))))
(assert (forall ((a7 Int)(_$ Int)(a8 Int)) (=> (and (= a7 0) (k3 a7) (= a8 0)) (k7 a8))))
(assert (forall ((a7 Int)(_$ Int)(a9 Int)(_$ Int)(a10 Int)) (=> (and (= a7 0) (k3 a7) (= a9 0) (k4 a9) (= a10 0)) (k8 a10))))
(assert (forall ((a7 Int)(_$ Int)(a9 Int)(_$ Int)(a11 Int)(_$ Int)) (=> (and (= a7 0) (k3 a7) (= a9 0) (k4 a9) (k5 a11)) (k9 a11))))
(assert (forall ((a12 Int)(_$ Int)(a13 Int)(_$ Int)(a14 Int)(_$ Int)(a15 Int)(_$ Int)) (=> (and (= a12 0) (k6 a12) (= a13 0) (k7 a13) (= a14 0) (k8 a14) (k9 a15) (not (> a15 0))) false)))

(check-sat)
