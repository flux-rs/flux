(set-logic HORN)

;; Tag 0: Call at 48:5: 48:29 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Bool Int Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (= a2 (ite (< a0 a1) a0 a1)) (>= a2 0) (not (= a2 a0))) (k0 (= a2 a1) a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (= a2 (ite (< a0 a1) a0 a1)) (>= a2 0) (not (not (= a2 a0)))) (k0 true a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(a3 Bool)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (= a2 (ite (< a0 a1) a0 a1)) (>= a2 0) (k0 a3 a0 a1 a2) (not (= a3 true))) false)))

(check-sat)
