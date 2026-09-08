(set-logic HORN)

;; Tag 0: Subtype(Input) at 14:5: 14:19 (ESpan { span: tests/pos/surface/fndef02.rs:3:17: 3:22 (#0), base: None })
;; Tag 1: Ret at 14:5: 14:19 (ESpan { span: tests/pos/surface/fndef02.rs:12:19: 12:20 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (> a0 0))) false)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (div 1 a0)))))
(assert (=> true (k0 10)))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (= a1 0))) false)))

(check-sat)
