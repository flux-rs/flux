(set-logic HORN)

;; Tag 0: Assert("possible out-of-bounds access") at 21:19: 21:26

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Par0) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(_$ Int)) (=> (>= a0 0) (k0 0 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)) (=> (>= a0 0) (k1 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (k0 (fld0$0 a1) (fld0$1 a1) a0) (k1 (fld0$1 a1) a0) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (not (< a3 a0))) false)))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (>= a0 0) (k0 (fld0$0 a1) (fld0$1 a1) a0) (k1 (fld0$1 a1) a0) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (< a3 a0) (> a4 666)) (k0 (fld0$0 a2) (fld0$1 a2) a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)(a1 (Adt0 Int))(_$ Int)(a2 (Adt0 Int))(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (>= a0 0) (k0 (fld0$0 a1) (fld0$1 a1) a0) (k1 (fld0$1 a1) a0) (=> (< (fld0$0 a1) (fld0$1 a1)) (= (fld0$0 a2) (+ (fld0$0 a1) 1))) (=> (not (< (fld0$0 a1) (fld0$1 a1))) (= (fld0$0 a2) (fld0$0 a1))) (= (fld0$1 a2) (fld0$1 a1)) (= (mkadt1$0 (< (fld0$0 a1) (fld0$1 a1))) (mkadt1$0 true)) (= a3 (fld0$0 a1)) (>= a3 0) (< a3 a0) (> a4 666)) (k1 (fld0$1 a2) a0))))

(check-sat)
