(set-logic HORN)

;; Tag 0: Ret at 3:5: 3:11 (ESpan { span: tests/pos/array/array00.rs:1:30: 1:36 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (=> true (k0 1)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (>= a0 0))) false)))

(check-sat)
