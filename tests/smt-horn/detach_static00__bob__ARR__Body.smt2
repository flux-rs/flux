(set-logic HORN)

;; Tag 0: Ret at 9:30: 9:39 (ESpan { span: tests/pos/detached/detach_static00.rs:23:30: 23:36 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 1)))
(assert (=> true (k0 2)))
(assert (=> true (k0 3)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (< a0 10))) false)))

(check-sat)
