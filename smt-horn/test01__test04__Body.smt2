(set-logic HORN)

;; Tag 0: Call at 31:5: 31:20 (ESpan { span: tests/pos/abstract_refinements/test01.rs:24:44: 24:49 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (=> true (k0 10 0)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (and (k0 a0 a1) (not (> a0 0))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (> a0 0) (k0 a0 a1))))

(check-sat)
