(set-logic HORN)

;; Tag 0: Call at 25:9: 25:20 (ESpan { span: tests/pos/surface/strg_to_mut.rs:5:35: 5:40 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)) (=> (> (fld0$0 a0) 0) (k0 (fld0$0 a0) (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(a1 Adt0)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (k0 (fld0$0 a1) (fld0$0 a0)) (not (> (fld0$0 a1) 0))) false)))
(assert (forall ((a0 Adt0)(_$ Int)(a1 Adt0)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (k0 (fld0$0 a1) (fld0$0 a0)) (> (fld0$0 a2) 0)) (k0 (fld0$0 a2) (fld0$0 a0)))))

(check-sat)
