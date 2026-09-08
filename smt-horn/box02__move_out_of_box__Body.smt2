(set-logic HORN)

;; Tag 0: Ret at 8:1: 8:2 (ESpan { span: tests/pos/surface/box02.rs:1:32: 1:38 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)
(declare-fun k3 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (=> true (k1 0)))
(assert (forall ((a1 Int)) (=> (= a1 0) (k2 a1))))
(assert (forall ((a2 Int)(_$ Int)) (=> (k1 a2) (k3 a2))))
(assert (forall ((a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (= a3 0) (k2 a3) (k3 a4) (not (>= a4 0))) false)))

(check-sat)
