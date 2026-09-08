(set-logic HORN)

;; Tag 0: Call at 9:5: 9:26 (ESpan { span: tests/pos/abstract_refinements/test04.rs:20:23: 20:29 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (>= a0 0))) false)))
(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k0 a0))))

(check-sat)
