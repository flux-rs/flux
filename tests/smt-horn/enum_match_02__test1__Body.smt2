(set-logic HORN)

;; Tag 0: Ret at 8:5: 8:20 (ESpan { span: tests/pos/structs/../../lib/nat.rs:1:44: 1:50 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 (+ 5 7))))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (<= 0 a0))) false)))

(check-sat)
