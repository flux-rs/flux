(set-logic HORN)

;; Tag 0: Call at 31:5: 31:27 (ESpan { span: tests/pos/surface/refined_fn_in_trait_01.rs:26:21: 26:25 (#0), base: None })
;; Tag 1: Call at 32:5: 32:27 (ESpan { span: tests/pos/surface/refined_fn_in_trait_01.rs:26:21: 26:25 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (=> true (k0 42)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= (= a0 42) true))) false)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 42 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (k1 a1 a0) (not (= (= a1 42) true))) false)))

(check-sat)
