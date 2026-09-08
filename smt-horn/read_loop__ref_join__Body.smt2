(set-logic HORN)

;; Tag 0: Call at 14:5: 14:23 (ESpan { span: tests/pos/surface/read_loop.rs:1:21: 1:25 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Bool) Bool)

(assert (forall ((a0 Bool)) (=> true (k0 0 a0))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a0) (not a0) (not (= (> (+ a1 1) 0) true))) false)))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a1 a0) a0) (k0 1 true))))

(check-sat)
