(set-logic HORN)

;; Tag 0: Ret at 39:5: 39:10 (ESpan { span: tests/pos/structs/struct-join.rs:30:46: 30:51 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Bool Int) Bool)

(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (not a0) (>= (fld0$0 a1) 0)) (k0 (fld0$0 a1) a0 (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and a0 (>= (fld0$0 a1) 0)) (k0 0 true (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(a2 Int)(_$ Int)) (=> (and (k0 a2 a0 (fld0$0 a1)) (not (> (+ a2 1) 0))) false)))

(check-sat)
