(set-logic HORN)

;; Tag 0: Call at 10:19: 10:22 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })
;; Tag 1: Ret at 11:5: 11:7 (ESpan { span: tests/pos/surface/test02.rs:5:30: 5:35 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (forall ((_$ Int)) (=> true (k0 1))))
(assert (forall ((_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (k0 a0)) (k1 a0))))
(assert (forall ((_$ Int)(_$ Int)) (=> (<= 0 (+ 0 1)) (k1 2))))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (k1 a1)) (k2 a1))))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (not (< 1 (+ (+ 0 1) 1)))) false)))
(assert (forall ((_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (+ 0 1)) (<= 0 (+ (+ 0 1) 1)) (>= a2 0) (k2 a2) (not (> a2 0))) false)))

(check-sat)
