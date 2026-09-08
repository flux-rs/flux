(set-logic HORN)

;; Tag 0: Ret at 10:5: 10:10 (ESpan { span: tests/pos/surface/slice00.rs:8:54: 8:60 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (>= a0 0) (> a1 0)) (k0 a1 a0))))
(assert (forall ((a0 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a2 a0) (not (>= a2 0))) false)))

(check-sat)
