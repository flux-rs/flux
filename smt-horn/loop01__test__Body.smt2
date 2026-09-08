(set-logic HORN)

;; Tag 0: Ret at 12:5: 12:8 (ESpan { span: tests/pos/surface/loop01.rs:4:22: 4:26 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 0 0)))
(assert (=> true (k1 0)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (not (< a0 100)) (not (<= 0 a1))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (< a0 100)) (k0 (+ a0 1) (+ a1 1)))))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1) (k1 a1) (< a0 100)) (k1 (+ a1 1)))))

(check-sat)
