(set-logic HORN)

;; Tag 0: Ret at 24:12: 24:25 (ESpan { span: tests/pos/surface/closure02.rs:20:57: 20:61 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)
;; orig: $k2
(declare-fun k2 (Int) Bool)
;; orig: $k3
(declare-fun k3 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (+ (+ a0 1) 2) a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (k2 a1) (k0 a1))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k2 a1) (k1 a2 a1)) (k3 a2))))
(assert (forall ((a3 Int)(_$ Int)) (=> (<= 0 a3) (k2 a3))))
(assert (forall ((a4 Int)(_$ Int)) (=> (and (k3 a4) (not (<= 3 a4))) false)))

(check-sat)
