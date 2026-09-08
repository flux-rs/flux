(set-logic HORN)

;; Tag 0: Ret at 22:5: 22:12 (ESpan { span: tests/pos/array/array02.rs:18:28: 18:34 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 42)))
(assert (=> true (k0 42)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (k0 a0) (not (>= a0 0))) false)))

(check-sat)
