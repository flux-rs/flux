(set-logic HORN)

;; Tag 0: Call at 5:6: 5:23 (ESpan { span: tests/pos/surface/ref_cell00.rs:3:32: 3:38 (#0), base: None })
;; Tag 1: Ret at 5:5: 5:23 (ESpan { span: tests/pos/surface/ref_cell00.rs:3:52: 3:58 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k0 a1) (not (>= a1 0))) false)))
(assert (forall ((a2 Int)(_$ Int)) (=> (k0 a2) (k1 a2))))
(assert (forall ((a3 Int)(_$ Int)) (=> (k1 a3) (k0 a3))))
(assert (forall ((a4 Int)(_$ Int)) (=> (and (k1 a4) (not (>= a4 0))) false)))

(check-sat)
