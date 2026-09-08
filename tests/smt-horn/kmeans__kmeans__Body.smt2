(set-logic HORN)

;; Tag 0: Ret at 125:1: 125:2
;; Tag 1: Call at 121:15: 121:38

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0))) (k0 0 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(a2 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0)) (= a2 (mkadt0$0 reftgen$n$0))) (k1 (fld0$0 a2) 0 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(a3 Int)(_$ Int)(_$ Int)(a4 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0)) (k0 a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (not (< a3 a1)) (k1 (fld0$0 a4) a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (not (= a4 (mkadt0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(a3 Int)(_$ Int)(_$ Int)(a5 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0)) (k0 a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (< a3 a1) (k1 (fld0$0 a5) a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (not (= a5 (mkadt0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0)) (k0 a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (< a3 a1)) (k0 (+ a3 1) reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a6 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$k$1)) (<= 0 (fld0$0 a0)) (k0 a3 reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1) (< a3 a1) (= a6 (mkadt0$0 reftgen$n$0))) (k1 (fld0$0 a6) (+ a3 1) reftgen$n$0 (fld0$0 reftgen$k$1) (fld0$0 a0) a1))))

(check-sat)
