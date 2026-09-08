(set-logic HORN)

;; Tag 0: Ret at 15:5: 15:7 (ESpan { span: tests/pos/array/array02.rs:9:28: 9:34 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (=> true (k0 0)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (k0 a0) (k0 (+ a0 1)))))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a0) (k0 a1) (k0 a2) (not (>= a1 0))) false)))

(check-sat)
