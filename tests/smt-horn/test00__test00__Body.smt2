(set-logic HORN)

;; Tag 0: Ret at 13:5: 13:15 (ESpan { span: tests/pos/abstract_refinements/test00.rs:11:28: 11:38 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 4)))
(assert (=> true (k0 10)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (>= a0 4) (>= a0 10) (not (= (mod a0 2) 0))) false)))

(check-sat)
