(set-logic HORN)

;; Tag 0: Ret at 12:5: 12:6 (ESpan { span: tests/pos/abstract_refinements/test03.rs:10:33: 10:38 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$x$0 Int)(a0 Int)(_$ Int)) (=> (and (k0 a0 reftgen$x$0) (not (< a0 reftgen$x$0))) false)))
(assert (forall ((reftgen$x$0 Int)(a0 Int)(_$ Int)) (=> (< a0 reftgen$x$0) (k0 a0 reftgen$x$0))))

(check-sat)
