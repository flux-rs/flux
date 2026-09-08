(set-logic HORN)

;; Tag 0: Ret at 13:22: 19:2

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((a0 Int)) (=> true (k0 a0 a0))))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (= a1 a0) (k1 a1 a0 a0))))
(assert (forall ((a0 Int)(a2 Adt0)(_$ Int)(a3 Int)(_$ Int)) (=> (and (k0 (fld0$0 a2) a0) (k1 a3 (fld0$0 a2) a0) (not (= a3 (fld0$0 a2)))) false)))

(check-sat)
