(set-logic HORN)

;; Tag 0: Call at 19:5: 19:30 (ESpan { span: tests/pos/structs/opaque-struct01.rs:5:21: 5:25 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int Bool) Bool)
(declare-fun k1 (Int Int Int Bool) Bool)

(assert (forall ((a0 Adt0)(a1 Bool)(_$ Int)) (=> (not a1) (k0 1 2 (fld0$0 a0) (fld0$1 a0) a1))))
(assert (forall ((a0 Adt0)(a1 Bool)(_$ Int)) (=> (not a1) (k1 2 (fld0$0 a0) (fld0$1 a0) a1))))
(assert (forall ((a0 Adt0)(a1 Bool)(_$ Int)) (=> a1 (k0 0 1 (fld0$0 a0) (fld0$1 a0) true))))
(assert (forall ((a0 Adt0)(a1 Bool)(_$ Int)) (=> a1 (k1 1 (fld0$0 a0) (fld0$1 a0) true))))
(assert (forall ((a0 Adt0)(a1 Bool)(a2 Int)(a3 Int)(_$ Int)) (=> (and (k0 a2 a3 (fld0$0 a0) (fld0$1 a0) a1) (k1 a3 (fld0$0 a0) (fld0$1 a0) a1) (not (= (> a3 a2) true))) false)))

(check-sat)
