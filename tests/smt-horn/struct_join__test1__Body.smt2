(set-logic HORN)

;; Tag 0: Ret at 15:5: 15:13 (ESpan { span: tests/pos/structs/struct-join.rs:8:40: 8:46 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Bool Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Bool Int) Bool)

(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)(a2 Int)) (=> (and (not a0) (>= (fld0$0 a1) 0)) (k0 (fld0$0 a1) a2 a0 (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)(a2 Int)) (=> (and (not a0) (>= (fld0$0 a1) 0)) (k1 a2 a0 (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)(a3 Int)) (=> (and a0 (>= (fld0$0 a1) 0)) (k0 (- (fld0$0 a1) 1) a3 true (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(_$ Int)(_$ Int)(a3 Int)) (=> (and a0 (>= (fld0$0 a1) 0)) (k1 a3 true (fld0$0 a1)))))
(assert (forall ((a0 Bool)(a1 Adt0)(a4 Int)(a5 Int)(_$ Int)) (=> (and (k0 a4 a5 a0 (fld0$0 a1)) (k1 a5 a0 (fld0$0 a1)) (not (>= (+ a4 1) 0))) false)))

(check-sat)
