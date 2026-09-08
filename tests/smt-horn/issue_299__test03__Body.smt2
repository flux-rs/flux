(set-logic HORN)

;; Tag 0: Assign at 48:5: 48:19 (ESpan { span: tests/pos/surface/issue-299.rs:20:26: 20:31 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int Int Int) Bool)

(assert (forall ((a0 Adt0)(a1 Adt0)) (=> true (k0 (fld0$0 a0) (fld0$1 a0) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)))))
(assert (forall ((a0 Adt0)(a1 Adt0)) (=> true (k1 (fld0$1 a0) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)))))
(assert (forall ((a0 Adt0)(a1 Adt0)) (=> true (k0 (fld0$0 a1) (fld0$1 a1) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)))))
(assert (forall ((a0 Adt0)(a1 Adt0)) (=> true (k1 (fld0$1 a1) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)))))
(assert (forall ((a0 Adt0)(a1 Adt0)(_$ Int)(a2 Adt0)(_$ Int)(a3 Int)(a4 Adt0)(_$ Int)(_$ Int)(a5 Adt0)(_$ Int)(a6 Int)(_$ Int)(a7 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a2) (fld0$1 a2) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$1 a2) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k0 (fld0$0 a4) (fld0$1 a4) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$1 a4) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k0 (fld0$0 a5) (fld0$1 a5) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$1 a5) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (> a6 0) (k0 (fld0$0 a7) (fld0$1 a7) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$1 a7) (fld0$0 a0) (fld0$1 a0) (fld0$0 a1) (fld0$1 a1)) (not (> (+ a6 1) 0))) false)))

(check-sat)
