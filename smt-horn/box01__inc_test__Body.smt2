(set-logic HORN)

;; Tag 0: Ret at 26:1: 26:2 (ESpan { span: tests/pos/surface/box01.rs:21:30: 21:33 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)) (=> true (k0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)) (=> (and (k0 a0 reftgen$n$0) (not (= (+ a0 1) (+ reftgen$n$0 1)))) false)))

(check-sat)
