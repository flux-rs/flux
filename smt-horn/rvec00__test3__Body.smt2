(set-logic HORN)

;; Tag 0: Call at 23:14: 23:17 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 1: Call at 24:18: 24:21 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (forall ((_$ Int)) (=> true (k0 0))))
(assert (forall ((_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (k0 a0)) (k1 a0))))
(assert (forall ((_$ Int)(_$ Int)) (=> (<= 0 (+ 0 1)) (k1 1))))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (k1 a1)) (k2 a1))))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (not (< 0 (+ (+ 0 1) 1)))) false)))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (k2 a2) (>= a2 0) (not (< 1 (+ (+ 0 1) 1)))) false)))

(check-sat)
