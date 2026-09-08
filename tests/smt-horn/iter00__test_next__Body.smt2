(set-logic HORN)

;; Tag 0: Call at 11:9: 11:38 (ESpan { span: tests/pos/surface/iter00.rs:5:21: 5:25 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int) Bool)
;; orig: $k0
(declare-fun k1 (Bool Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (= a1 0) (k0 a1) (<= 10 a2) (< a2 15)) (k1 true a2))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Bool)(_$ Int)) (=> (and (= a1 0) (k0 a1) (<= 10 a2) (< a2 15) (k1 a3 a2) (not (= a3 true))) false)))

(check-sat)
