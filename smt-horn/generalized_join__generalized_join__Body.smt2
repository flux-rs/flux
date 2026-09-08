(set-logic HORN)

;; Tag 0: Ret at 9:5: 9:10 (ESpan { span: tests/pos/surface/generalized_join.rs:1:28: 1:29 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)) (=> true (k0 0 0 a0))))
(assert (forall ((a0 Int)) (=> true (k1 0 a0))))
(assert (forall ((a0 Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a2 a0) (k1 a2 a0) (not (< a1 a0)) (not (= (- a1 a2) 0))) false)))
(assert (forall ((a0 Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a2 a0) (k1 a2 a0) (< a1 a0)) (k0 (+ a1 1) (+ a2 1) a0))))
(assert (forall ((a0 Int)(a1 Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a2 a0) (k1 a2 a0) (< a1 a0)) (k1 (+ a2 1) a0))))

(check-sat)
