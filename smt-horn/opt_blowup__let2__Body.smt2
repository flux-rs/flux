(set-logic HORN)

;; Tag 0: Ret at 61:5: 61:14 (ESpan { span: tests/pos/surface/opt_blowup.rs:51:36: 51:41 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (< reftgen$n$0 a0) (< a0 a1)) (k0 a1 reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (< reftgen$n$0 a0) (< a0 a1) (k0 a2 reftgen$n$0 a0 a1) (not (< reftgen$n$0 a2))) false)))

(check-sat)
