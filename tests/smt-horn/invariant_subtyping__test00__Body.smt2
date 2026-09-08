(set-logic HORN)

;; Tag 0: Call at 4:5: 4:34

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= a0 0))) false)))
(assert (forall ((a1 Int)(_$ Int)) (=> (= a1 0) (k0 a1))))

(check-sat)
