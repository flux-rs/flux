(set-logic HORN)

;; Tag 0: Ret at 41:5: 41:7 (ESpan { span: tests/pos/surface/box02.rs:30:33: 30:38 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Bool) Bool)
(declare-fun k1 (Int Bool Int) Bool)

(assert (forall ((a0 Bool)) (=> true (k0 1 a0))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a0) (not a0)) (k1 (+ (+ a1 1) 2) a0 a1))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a0) a0) (k1 (+ (+ a1 1) 1) true a1))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a1 a0) (k1 a2 a0 a1) (not (> a2 2))) false)))

(check-sat)
