(set-logic HORN)

;; Tag 0: Subtype(Output) at 22:5: 22:19 (ESpan { span: tests/pos/surface/closure04.rs:13:77: 13:83 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (<= 0 a1) (k0 a1))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 a1) (k1 a2 a1) (not (<= 0 a2))) false)))

(check-sat)
