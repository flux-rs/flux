(set-logic HORN)

;; Tag 0: Subtype(Output) at 12:5: 12:31 (ESpan { span: tests/pos/surface/closure05.rs:2:66: 2:71 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int Int Int) Bool)

(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1)) (k2 (+ (+ a0 a1) 10) a0 a1))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (<= 0 a2) (<= 0 a3)) (k0 a2 a3))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (<= 0 a2) (<= 0 a3)) (k1 a3))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (<= 0 a2) (<= 0 a3) (k2 a4 a2 a3) (not (<= 10 a4))) false)))

(check-sat)
