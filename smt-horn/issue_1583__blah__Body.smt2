(set-logic HORN)

;; Tag 0: Assert("possible out-of-bounds access") at 14:16: 14:22

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Par0) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (=> true (k0 0 0 10)))
(assert (=> true (k1 0 10)))
(assert (=> true (k2 10)))
(assert (forall ((a0 Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$0 a1) (fld0$1 a1)) (k2 (fld0$1 a1)) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (not (< a3 10))) false)))
(assert (forall ((a0 Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$0 a1) (fld0$1 a1)) (k2 (fld0$1 a1)) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (< a3 10)) (k0 (+ a0 a4) (fld0$0 a2) (fld0$1 a2)))))
(assert (forall ((a0 Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$0 a1) (fld0$1 a1)) (k2 (fld0$1 a1)) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (< a3 10)) (k1 (fld0$0 a2) (fld0$1 a2)))))
(assert (forall ((a0 Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$1 a1)) (k1 (fld0$0 a1) (fld0$1 a1)) (k2 (fld0$1 a1)) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (< a3 10)) (k2 (fld0$1 a2)))))

(check-sat)
