(set-logic HORN)

;; Tag 0: Ret at 10:5: 10:6

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (+ a0 1)))))
(assert (forall ((a1 Int)(_$ Int)) (=> (= a1 99) (k0 a1))))
(assert (forall ((a2 Int)(_$ Int)) (=> (and (k1 a2) (not (= a2 100))) false)))

(check-sat)
