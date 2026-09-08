(set-logic HORN)

;; Tag 0: Call at 35:22: 35:40 (ESpan { span: tests/pos/surface/closure02.rs:28:26: 28:33 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Bool) Bool)
(declare-fun k1 (Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)(_$ Int)) (=> (and (k0 a0) a0 (not (<= 10 (+ 6 10)))) false)))
(assert (forall ((a1 Bool)(_$ Int)) (=> (k1 a1) (k0 a1))))
(assert (forall ((a2 Bool)) (=> true (k1 a2))))

(check-sat)
