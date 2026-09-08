(set-logic HORN)

;; Tag 0: Ret at 15:5: 15:11 (ESpan { span: tests/pos/array/array04.rs:12:23: 12:29 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= a0 0))) false)))

(check-sat)
