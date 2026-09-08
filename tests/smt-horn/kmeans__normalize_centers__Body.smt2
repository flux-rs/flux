(set-logic HORN)

;; Tag 0: Call at 87:23: 87:26

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k2
(declare-fun k1 (Int Int Int Int) Bool)
;; orig: $k3
(declare-fun k2 (Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0)) (k0 0 reftgen$n$0 (fld0$0 reftgen$k$1)))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 reftgen$n$0 (fld0$0 reftgen$k$1)) (< a0 (fld0$0 reftgen$k$1)) (= a1 (mkadt0$0 reftgen$n$0))) (k1 (fld0$0 a1) reftgen$n$0 (fld0$0 reftgen$k$1) a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 reftgen$n$0 (fld0$0 reftgen$k$1)) (< a0 (fld0$0 reftgen$k$1)) (k1 (fld0$0 a2) reftgen$n$0 (fld0$0 reftgen$k$1) a0) (not (= a2 (mkadt0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a3 Int)) (=> (and (>= reftgen$n$0 0) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 reftgen$n$0 (fld0$0 reftgen$k$1)) (< a0 (fld0$0 reftgen$k$1))) (k2 a3 reftgen$n$0 (fld0$0 reftgen$k$1) a0))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(_$ Int)(a5 Adt0)(_$ Int)(a6 Int)) (=> (and (>= reftgen$n$0 0) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 reftgen$n$0 (fld0$0 reftgen$k$1)) (< a0 (fld0$0 reftgen$k$1)) (k2 a4 reftgen$n$0 (fld0$0 reftgen$k$1) a0) (>= a4 0) (k1 (fld0$0 a5) reftgen$n$0 (fld0$0 reftgen$k$1) a0)) (k0 (+ a0 1) reftgen$n$0 (fld0$0 reftgen$k$1)))))

(check-sat)
