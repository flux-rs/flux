(set-logic HORN)

;; Tag 0: Ret at 36:5: 36:11 (ESpan { span: tests/pos/array/array04.rs:34:29: 34:34 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 1)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (> a0 0))) false)))

(check-sat)
