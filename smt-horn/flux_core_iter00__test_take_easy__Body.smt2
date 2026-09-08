(set-logic HORN)

;; Tag 0: Assert("possible out-of-bounds access") at 32:9: 32:23

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Int) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
(declare-fun c0 (Int Int) Bool)
(declare-fun c1 (Int) Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int Int) Bool)
(declare-fun k2 (Int Int Int) Bool)

(assert (forall ((_$ Int)(a0 Int)(a1 Int)) (=> true (k0 0 5 a1 a0 a1))))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)) (=> true (k1 5 a1 a0 a1))))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)) (=> true (k2 a1 a0 a1))))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)) (=> (and (k0 a2 (fld0$0 a3) (fld0$1 a3) a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) a0 a1) (k2 (fld0$1 a3) a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (not (< a2 100))) false)))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a2 (fld0$0 a3) (fld0$1 a3) a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) a0 a1) (k2 (fld0$1 a3) a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 100)) (k0 (+ a2 1) (fld0$0 a4) (fld0$1 a4) a0 a1))))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a2 (fld0$0 a3) (fld0$1 a3) a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) a0 a1) (k2 (fld0$1 a3) a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 100)) (k1 (fld0$0 a4) (fld0$1 a4) a0 a1))))
(assert (forall ((_$ Int)(a0 Int)(a1 Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a2 (fld0$0 a3) (fld0$1 a3) a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) a0 a1) (k2 (fld0$1 a3) a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 100)) (k2 (fld0$1 a4) a0 a1))))

(check-sat)
