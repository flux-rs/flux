(set-logic HORN)

;; Tag 0: Call at 15:22: 15:39 (ESpan { span: tests/pos/surface/slice00.rs:13:30: 13:35 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (>= a0 0) (> a1 0)) (k0 a1 a0))))
(assert (forall ((a0 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a2 a0) (not (> a2 0))) false)))
(assert (forall ((a0 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a3 a0)) (k0 (+ a3 1) a0))))

(check-sat)
