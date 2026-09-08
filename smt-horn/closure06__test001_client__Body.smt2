(set-logic HORN)

;; Tag 0: Subtype(Output) at 13:5: 13:27 (ESpan { span: tests/pos/surface/closure06.rs:2:53: 2:59 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (+ a0 1) a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (<= 10 a1) (k0 a1))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 10 a1) (k1 a2 a1) (not (<= 10 a2))) false)))

(check-sat)
