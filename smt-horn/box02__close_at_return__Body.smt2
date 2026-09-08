(set-logic HORN)

;; Tag 0: Ret at 16:5: 16:6 (ESpan { span: tests/pos/surface/box02.rs:10:29: 10:30 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 1)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= (+ a0 1) 2))) false)))

(check-sat)
