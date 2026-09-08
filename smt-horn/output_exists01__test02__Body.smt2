(set-logic HORN)

;; Tag 0: Ret at 43:5: 46:6

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$1 Int)) (=> true (k0 reftgen$n$1 reftgen$n$1 reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)) (=> true (k1 reftgen$n$1 reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) (not a2) (not (= a1 a0))) false)))
(assert (forall ((reftgen$n$1 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) a2) (k0 (+ a0 1) (+ a1 1) reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)(a0 Int)(a1 Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) a2) (k1 (+ a1 1) reftgen$n$1))))

(check-sat)
