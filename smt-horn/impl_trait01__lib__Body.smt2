(set-logic HORN)

;; Tag 0: Ret at 3:5: 3:12 (ESpan { span: tests/pos/impl_trait/impl_trait01.rs:1:54: 1:58 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$x$0 Int)) (=> true (k0 reftgen$x$0 reftgen$x$0))))
(assert (forall ((reftgen$x$0 Int)(a0 Int)(_$ Int)) (=> (k0 a0 reftgen$x$0) (k1 a0 reftgen$x$0))))
(assert (forall ((reftgen$x$0 Int)(a1 Int)(_$ Int)) (=> (and (k1 a1 reftgen$x$0) (not (<= reftgen$x$0 a1))) false)))

(check-sat)
