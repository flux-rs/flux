(set-logic HORN)

;; Tag 0: Ret at 57:5: 57:8
;; Tag 1: Ret at 57:5: 57:8 (ESpan { span: tests/pos/surface/kmeans.rs:49:65: 49:66 (#0), base: None })

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
;; orig: $k1
(declare-fun k2 (Int Int Int Int Int) Bool)
;; orig: $k3
(declare-fun k3 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0)) (k0 0 0 reftgen$n$0 reftgen$k$1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0)) (k1 0 reftgen$n$0 reftgen$k$1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (not (< a1 reftgen$k$1)) (k2 (fld0$0 a2) a0 a1 reftgen$n$0 reftgen$k$1) (not (= a2 (mkadt0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (not (< a1 reftgen$k$1)) (not (= a0 reftgen$k$1))) false)))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (< a1 reftgen$k$1) (<= 0 reftgen$n$0) (k2 (fld0$0 a3) a0 a1 reftgen$n$0 reftgen$k$1)) (k3 (fld0$0 a3) reftgen$n$0 reftgen$k$1 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (< a1 reftgen$k$1) (<= 0 reftgen$n$0)) (k3 reftgen$n$0 reftgen$n$0 reftgen$k$1 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (< a1 reftgen$k$1) (<= 0 reftgen$n$0) (<= 0 (+ a0 1))) (k0 (+ a0 1) (+ a1 1) reftgen$n$0 reftgen$k$1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (< a1 reftgen$k$1) (<= 0 reftgen$n$0) (<= 0 (+ a0 1))) (k1 (+ a1 1) reftgen$n$0 reftgen$k$1))))
(assert (forall ((reftgen$n$0 Int)(reftgen$k$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a4 Adt0)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$k$1 0) (>= reftgen$k$1 0) (k0 a0 a1 reftgen$n$0 reftgen$k$1) (k1 a1 reftgen$n$0 reftgen$k$1) (< a1 reftgen$k$1) (<= 0 reftgen$n$0) (<= 0 (+ a0 1)) (k3 (fld0$0 a4) reftgen$n$0 reftgen$k$1 a0 a1)) (k2 (fld0$0 a4) (+ a0 1) (+ a1 1) reftgen$n$0 reftgen$k$1))))

(check-sat)
