(set-logic HORN)

;; Tag 0: Ret at 25:5: 25:10 (ESpan { span: tests/pos/surface/async00.rs:23:41: 23:47 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (>= a0 0))) false)))

(check-sat)
