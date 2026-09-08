(set-logic HORN)

;; Tag 0: Ret at 4:5: 4:11 (ESpan { span: tests/pos/surface/join04.rs:1:32: 1:37 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k2
(declare-fun k0 (Int Bool) Bool)
;; orig: $k0
(declare-fun k1 (Bool) Bool)
;; orig: $k1
(declare-fun k2 (Int Bool) Bool)
;; orig: $k3
(declare-fun k3 (Int Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 3 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 4 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k1 a0))))
(assert (forall ((a0 Bool)(_$ Int)(a1 Int)(_$ Int)) (=> (and (not a0) (k0 a1 a0)) (k2 a1 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k3 1 true))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k3 2 true))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k1 true))))
(assert (forall ((a0 Bool)(_$ Int)(a2 Int)(_$ Int)) (=> (and a0 (k3 a2 true)) (k2 a2 true))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (k1 a0) (k2 a3 a0) (not (> a3 0))) false)))

(check-sat)
