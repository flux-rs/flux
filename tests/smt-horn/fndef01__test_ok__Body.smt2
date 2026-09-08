(set-logic HORN)

;; Tag 0: Ret at 9:5: 9:6

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

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (k1 a1)) (k2 a1))))
(assert (forall ((a2 Int)(_$ Int)) (=> (= a2 99) (k0 a2))))
(assert (forall ((a3 Int)(_$ Int)) (=> (and (k2 a3) (not (= a3 99))) false)))

(check-sat)
