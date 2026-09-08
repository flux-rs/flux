(set-logic HORN)

;; Tag 0: Ret at 57:1: 57:2 (ESpan { span: tests/pos/enums/list01.rs:51:48: 51:79 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (Set Int))))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 ((Set Int) (Set Int) (Set Int)) Bool)
(declare-fun k1 ((Set Int) (Set Int) (Set Int) Int (Set Int)) Bool)

(assert (forall ((reftgen$xs1$0 Adt0)(reftgen$xs2$1 Adt0)(_$ Int)) (=> (= reftgen$xs1$0 (mkadt0$0 (as emptyset 0))) (k0 (fld0$0 reftgen$xs2$1) (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1)))))
(assert (forall ((reftgen$xs1$0 Adt0)(reftgen$xs2$1 Adt0)(a0 Int)(a1 Adt0)(_$ Int)) (=> (= reftgen$xs1$0 (mkadt0$0 (union (singleton a0) (fld0$0 a1)))) (k1 (union (fld0$0 a1) (fld0$0 reftgen$xs2$1)) (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1) a0 (fld0$0 a1)))))
(assert (forall ((reftgen$xs1$0 Adt0)(reftgen$xs2$1 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (= reftgen$xs1$0 (mkadt0$0 (union (singleton a0) (fld0$0 a1)))) (k1 (fld0$0 a2) (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1) a0 (fld0$0 a1))) (k0 (union (singleton a0) (fld0$0 a2)) (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1)))))
(assert (forall ((reftgen$xs1$0 Adt0)(reftgen$xs2$1 Adt0)(a3 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a3) (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1)) (not (= (fld0$0 a3) (union (fld0$0 reftgen$xs1$0) (fld0$0 reftgen$xs2$1))))) false)))

(check-sat)
