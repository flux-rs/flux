(set-logic HORN)

;; Tag 0: Subtype(Output) at 12:5: 12:21

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (+ a0 1) a0))))
(assert (forall ((a1 Int)) (=> true (k0 a1))))
(assert (forall ((a1 Int)(a2 Int)(_$ Int)) (=> (and (k1 a2 a1) (not (= a2 (+ a1 1)))) false)))

(check-sat)
