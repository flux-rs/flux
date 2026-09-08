(set-logic HORN)

;; Tag 0: Ret at 8:21: 8:29 (ESpan { span: tests/with_deps/pos/ptr_cast_1700.rs:4:30: 4:47 (#0), base: None })
;; Tag 1: Ret at 8:21: 8:29 (ESpan { span: tests/with_deps/pos/ptr_cast_1700.rs:4:51: 4:68 (#0), base: None })
;; Tag 2: Ret at 8:21: 8:29 (ESpan { span: tests/with_deps/pos/ptr_cast_1700.rs:4:72: 4:89 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)(Tuple3 3)) (((mkadt0$0 (fld0$0 Bool)))((mkadt1$0 (fld1$0 Int) (fld1$1 Int) (fld1$2 Int)))(par (Par0 Par1 Par2) ((mktuple3 (tuple3$0 Par0) (tuple3$1 Par1) (tuple3$2 Par2))))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int Int Int Int) Bool)

(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0))) (k0 (fld1$0 a0) (fld1$1 a0) (fld1$2 a0) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)))))
(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0))) (k1 (fld1$1 a0) (fld1$2 a0) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)))))
(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0))) (k2 (fld1$2 a0) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)))))
(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)(a1 Adt1)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0)) (k0 (fld1$0 a1) (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k1 (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k2 (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (not (= (fld1$0 a1) (tuple3$0 reftgen$p$0)))) false)))
(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)(a1 Adt1)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0)) (k0 (fld1$0 a1) (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k1 (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k2 (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (not (= (fld1$1 a1) (tuple3$1 reftgen$p$0)))) false)))
(assert (forall ((reftgen$p$0 (Tuple3 Int Int Int))(_$ Int)(a0 Adt1)(_$ Int)(_$ Int)(a1 Adt1)(_$ Int)) (=> (and (= (mkadt0$0 (not (= (tuple3$1 reftgen$p$0) 0))) (mkadt0$0 true)) (= a0 (mkadt1$0 (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0))) (not (= (fld1$1 a0) 0)) (k0 (fld1$0 a1) (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k1 (fld1$1 a1) (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (k2 (fld1$2 a1) (tuple3$0 reftgen$p$0) (tuple3$1 reftgen$p$0) (tuple3$2 reftgen$p$0) (fld1$0 a0) (fld1$1 a0) (fld1$2 a0)) (not (= (fld1$2 a1) (tuple3$2 reftgen$p$0)))) false)))

(check-sat)
