(set-logic HORN)

;; Tag 0: Ret at 45:5: 45:6 (ESpan { span: tests/pos/surface/restrictable_variants.rs:34:38: 34:39 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt1 0)) (((mkadt1$0) (mkadt1$1) (mkadt1$2) (mkadt1$3) (mkadt1$4) (mkadt1$5))))
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 (Set Adt1))))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 ((Set Adt1) (Set Adt1)) Bool)
(declare-fun k1 ((Set Adt1) (Set Adt1) (Set Adt1)) Bool)

(assert (forall ((reftgen$s$0 Adt0)(_$ Int)(a0 Int)) (=> (= reftgen$s$0 (mkadt0$0 (union (as emptyset 0) (singleton mkadt1$0)))) (k0 (union (as emptyset 0) (singleton mkadt1$0)) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(_$ Int)(a1 Bool)) (=> (= reftgen$s$0 (mkadt0$0 (union (as emptyset 0) (singleton mkadt1$1)))) (k0 (union (as emptyset 0) (singleton mkadt1$1)) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a2 Adt0)(_$ Int)) (=> (= reftgen$s$0 (mkadt0$0 (union (fld0$0 a2) (union (as emptyset 0) (singleton mkadt1$2))))) (k0 (union (fld0$0 a2) (union (as emptyset 0) (singleton mkadt1$2))) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a3 Adt0)(a4 Adt0)(_$ Int)) (=> (= reftgen$s$0 (mkadt0$0 (union (union (fld0$0 a3) (fld0$0 a4)) (union (as emptyset 0) (singleton mkadt1$3))))) (k0 (union (union (fld0$0 a3) (fld0$0 a4)) (union (as emptyset 0) (singleton mkadt1$3))) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a5 Adt0)(a6 Adt0)(_$ Int)) (=> (= reftgen$s$0 (mkadt0$0 (union (union (fld0$0 a5) (fld0$0 a6)) (union (as emptyset 0) (singleton mkadt1$4))))) (k0 (union (union (fld0$0 a5) (fld0$0 a6)) (union (as emptyset 0) (singleton mkadt1$4))) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a7 Adt0)(a8 Adt0)(_$ Int)) (=> (= reftgen$s$0 (mkadt0$0 (union (union (fld0$0 a7) (fld0$0 a8)) (union (as emptyset 0) (singleton mkadt1$5))))) (k0 (union (union (fld0$0 a7) (fld0$0 a8)) (union (as emptyset 0) (singleton mkadt1$5))) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a9 (Set Adt1))(_$ Int)) (=> (k0 a9 (fld0$0 reftgen$s$0)) (k1 a9 (fld0$0 reftgen$s$0) a9))))
(assert (forall ((reftgen$s$0 Adt0)(a9 (Set Adt1))(_$ Int)(a10 Adt0)(_$ Int)) (=> (and (k0 a9 (fld0$0 reftgen$s$0)) (k1 (fld0$0 a10) (fld0$0 reftgen$s$0) a9) (not (= a10 reftgen$s$0))) false)))

(check-sat)
