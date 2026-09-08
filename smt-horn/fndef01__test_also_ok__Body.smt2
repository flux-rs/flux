(set-logic HORN)

;; Tag 0: Ret at 15:11: 15:12

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (k1 a1)) (k2 a1))))
(assert (forall ((a2 Int)(_$ Int)) (=> (= a2 99) (k0 a2))))
(assert (forall ((a3 Int)(_$ Int)) (=> (and (k2 a3) (not (= a3 99))) false)))

(check-sat)
