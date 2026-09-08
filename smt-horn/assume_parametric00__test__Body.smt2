(set-logic HORN)

;; Tag 0: Ret at 17:5: 17:12 (ESpan { span: tests/pos/surface/assume_parametric00.rs:15:40: 15:45 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (> a0 0) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k0 a1) (not (> a1 0))) false)))

(check-sat)
