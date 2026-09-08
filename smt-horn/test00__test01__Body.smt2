(set-logic HORN)

;; Tag 0: Ret at 19:5: 19:15 (ESpan { span: tests/pos/abstract_refinements/test00.rs:17:25: 17:27 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 4)))
(assert (=> true (k0 10)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (>= a0 4) (>= a0 10) (not (= a0 10))) false)))

(check-sat)
