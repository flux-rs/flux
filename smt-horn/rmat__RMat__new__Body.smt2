(set-logic HORN)

;; Tag 0: Call at 24:9: 24:29
;; Tag 1: Ret at 25:5: 25:6 (ESpan { span: tests/pos/surface/rmat.rs:15:59: 15:63 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int Int) Bool)
(declare-fun k3 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0)) (k0 0 0 reftgen$rows$0 reftgen$cols$1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0)) (k1 0 reftgen$rows$0 reftgen$cols$1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (not (< a1 reftgen$rows$0)) (k2 (fld0$0 a2) a0 a1 reftgen$rows$0 reftgen$cols$1) (not (= a2 (mkadt0$0 reftgen$cols$1)))) false)))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (not (< a1 reftgen$rows$0)) (not (= a0 reftgen$rows$0))) false)))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (< a1 reftgen$rows$0) (<= 0 reftgen$cols$1) (k2 (fld0$0 a3) a0 a1 reftgen$rows$0 reftgen$cols$1)) (k3 (fld0$0 a3) reftgen$rows$0 reftgen$cols$1 a0 a1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (< a1 reftgen$rows$0) (<= 0 reftgen$cols$1)) (k3 reftgen$cols$1 reftgen$rows$0 reftgen$cols$1 a0 a1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (< a1 reftgen$rows$0) (<= 0 reftgen$cols$1) (<= 0 (+ a0 1))) (k0 (+ a0 1) (+ a1 1) reftgen$rows$0 reftgen$cols$1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (< a1 reftgen$rows$0) (<= 0 reftgen$cols$1) (<= 0 (+ a0 1))) (k1 (+ a1 1) reftgen$rows$0 reftgen$cols$1))))
(assert (forall ((reftgen$rows$0 Int)(reftgen$cols$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a4 Adt0)(_$ Int)) (=> (and (>= reftgen$rows$0 0) (>= reftgen$cols$1 0) (k0 a0 a1 reftgen$rows$0 reftgen$cols$1) (k1 a1 reftgen$rows$0 reftgen$cols$1) (< a1 reftgen$rows$0) (<= 0 reftgen$cols$1) (<= 0 (+ a0 1)) (k3 (fld0$0 a4) reftgen$rows$0 reftgen$cols$1 a0 a1)) (k2 (fld0$0 a4) (+ a0 1) (+ a1 1) reftgen$rows$0 reftgen$cols$1))))

(check-sat)
