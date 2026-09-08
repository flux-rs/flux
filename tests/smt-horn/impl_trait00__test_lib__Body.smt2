(set-logic HORN)

;; Tag 0: Ret at 12:5: 12:13 (ESpan { span: tests/pos/impl_trait/impl_trait00.rs:10:49: 10:53 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 10)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (<= 1 a1))) false)))

(check-sat)
