(set-logic HORN)

;; Tag 0: Ret at 79:5: 79:8 (ESpan { span: tests/pos/surface/kmeans.rs:62:57: 62:62 (#0), base: None })
;; Tag 1: Call at 72:18: 72:33

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k3
(declare-fun k2 (Int Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k3 (Int Int Int Int Int Int Bool) Bool)

(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0)) (k0 0 0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0)) (k1 0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (not (< a1 (fld0$0 reftgen$k$1))) (not (< a0 (fld0$0 reftgen$k$1)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (= a2 reftgen$n$0)) (k2 (fld0$0 a2) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (k2 (fld0$0 a3) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1) (<= 0 (fld0$0 a3)) (not (= reftgen$n$0 a3))) false)))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)(a4 Bool)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (k2 (fld0$0 a3) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1) (<= 0 (fld0$0 a3)) (not a4)) (k3 a0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1 (fld0$0 a3) a4))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)(a4 Bool)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (k2 (fld0$0 a3) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1) (<= 0 (fld0$0 a3)) a4) (k3 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1 (fld0$0 a3) true))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)(a4 Bool)(a5 Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (k2 (fld0$0 a3) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1) (<= 0 (fld0$0 a3)) (k3 a5 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1 (fld0$0 a3) a4)) (k0 a5 (+ a1 1) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)))))
(assert (forall ((reftgen$n$0 Adt0)(reftgen$k$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)(a4 Bool)(a5 Int)(_$ Int)) (=> (and (> (fld0$0 reftgen$k$1) 0) (<= 0 (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 reftgen$k$1)) (>= (fld0$0 reftgen$k$1) 0) (k0 a0 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (k1 a1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)) (< a1 (fld0$0 reftgen$k$1)) (k2 (fld0$0 a3) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1) (<= 0 (fld0$0 a3)) (k3 a5 (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1) a0 a1 (fld0$0 a3) a4)) (k1 (+ a1 1) (fld0$0 reftgen$n$0) (fld0$0 reftgen$k$1)))))

(check-sat)
