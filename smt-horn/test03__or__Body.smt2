(set-logic HORN)

;; Tag 0: Ret at 17:5: 17:6 (ESpan { span: tests/pos/abstract_refinements/test03.rs:15:41: 15:55 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (Array Int Bool))))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int (Array Int Bool) (Array Int Bool)) Bool)

(assert (forall ((reftgen$p1$0 Adt0)(reftgen$p2$1 Adt0)(a0 Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 reftgen$p1$0) (fld0$0 reftgen$p2$1)) (not (or ((fld0$0 reftgen$p1$0) a0) ((fld0$0 reftgen$p2$1) a0)))) false)))
(assert (forall ((reftgen$p1$0 Adt0)(reftgen$p2$1 Adt0)(a0 Int)(_$ Int)) (=> (or ((fld0$0 reftgen$p1$0) a0) ((fld0$0 reftgen$p2$1) a0)) (k0 a0 (fld0$0 reftgen$p1$0) (fld0$0 reftgen$p2$1)))))

(check-sat)
