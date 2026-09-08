(set-logic HORN)

;; Tag 0: Ret at 15:5: 15:11

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int Bool) Bool)
(declare-fun k1 (Int Int Int Bool) Bool)

(assert (forall ((reftgen$p$0 Adt0)(a0 Bool)(_$ Int)) (=> (not a0) (k0 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) a0))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Bool)(_$ Int)) (=> (not a0) (k1 (fld0$1 reftgen$p$0) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) a0))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Bool)(_$ Int)) (=> a0 (k0 (fld0$0 reftgen$p$0) (+ (fld0$1 reftgen$p$0) 1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) true))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Bool)(_$ Int)) (=> a0 (k1 (+ (fld0$1 reftgen$p$0) 1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) true))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Bool)(a1 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a1) (fld0$1 a1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) a0) (k1 (fld0$1 a1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) a0) (not (= (fld0$0 a1) (fld0$0 reftgen$p$0)))) false)))

(check-sat)
