(set-logic HORN)

;; Tag 0: Ret at 22:9: 22:13 (ESpan { span: tests/pos/surface/associated_type02.rs:20:39: 20:44 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (> a0 0) (k0 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (> a0 0) (k0 a1 a0) (not (> a1 0))) false)))

(check-sat)
