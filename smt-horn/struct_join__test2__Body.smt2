(set-logic HORN)

;; Tag 0: Ret at 27:5: 27:10 (ESpan { span: tests/pos/structs/struct-join.rs:18:40: 18:45 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Bool Int) Bool)

(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)(a2 Int)) (=> (and (not a0) (>= (fld0$0 a1) 0)) (k0 (fld0$0 a1) a0 (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)) (=> a0 (k0 0 true (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(a3 Int)(_$ Int)) (=> (and (k0 a3 a0 (fld0$0 a1)) (not (> (+ a3 1) 0))) false)))

(check-sat)
