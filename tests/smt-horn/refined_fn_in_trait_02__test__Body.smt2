(set-logic HORN)

;; Tag 0: Call at 17:5: 17:27 (ESpan { span: tests/pos/surface/refined_fn_in_trait_02.rs:12:21: 12:25 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 42)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= (= a0 42) true))) false)))

(check-sat)
