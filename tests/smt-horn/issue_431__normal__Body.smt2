(set-logic HORN)

;; Tag 0: Ret at 18:5: 18:8

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= a0 0)) (k0 0 0 (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= a0 0)) (k1 0 (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= a0 0) (k0 a1 a2 (fld0$0 reftgen$n$0) a0) (k1 a2 (fld0$0 reftgen$n$0) a0) (>= (fld0$0 reftgen$n$0) 0) (not (< a1 (fld0$0 reftgen$n$0))) (not (= a2 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= a0 0) (k0 a1 a2 (fld0$0 reftgen$n$0) a0) (k1 a2 (fld0$0 reftgen$n$0) a0) (>= (fld0$0 reftgen$n$0) 0) (< a1 (fld0$0 reftgen$n$0)) (<= 0 (+ a2 1))) (k0 (+ a1 1) (+ a2 1) (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (>= a0 0) (k0 a1 a2 (fld0$0 reftgen$n$0) a0) (k1 a2 (fld0$0 reftgen$n$0) a0) (>= (fld0$0 reftgen$n$0) 0) (< a1 (fld0$0 reftgen$n$0)) (<= 0 (+ a2 1))) (k1 (+ a2 1) (fld0$0 reftgen$n$0) a0))))

(check-sat)
