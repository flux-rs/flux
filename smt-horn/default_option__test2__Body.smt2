(set-logic HORN)

;; Tag 0: Ret at 11:5: 11:8 (ESpan { span: tests/pos/structs/default-option.rs:8:27: 8:34 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 12)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (<= 10 a1))) false)))

(check-sat)
