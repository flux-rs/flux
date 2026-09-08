(set-logic HORN)

;; Tag 0: Call at 53:9: 53:27 (ESpan { span: tests/with_deps/pos/surface/for_range00.rs:6:25: 6:29 (#0), base: None })
;; Tag 1: Call at 48:13: 48:29 (ESpan { span: tests/with_deps/pos/surface/for_range00.rs:6:25: 6:29 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Par0) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k0
(declare-fun k2 (Int Int) Bool)
;; orig: $k1
(declare-fun k3 (Int Int Int Int Int Int Int Int Bool) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k0 0 0 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k1 0 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k2 a0 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 false)) (not (= (<= a1 a0) true))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) (not (= (<= a1 a4) true))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Bool)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) (not a5)) (k3 a1 a0 a1 (fld0$0 a2) (fld0$1 a2) (fld0$0 a3) (fld0$1 a3) a4 a5))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Bool)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) a5) (k3 (+ a1 1) a0 a1 (fld0$0 a2) (fld0$1 a2) (fld0$0 a3) (fld0$1 a3) a4 true))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Bool)(a6 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) (k3 a6 a0 a1 (fld0$0 a2) (fld0$1 a2) (fld0$0 a3) (fld0$1 a3) a4 a5)) (k0 a6 (fld0$0 a3) (fld0$1 a3) a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Bool)(a6 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) (k3 a6 a0 a1 (fld0$0 a2) (fld0$1 a2) (fld0$0 a3) (fld0$1 a3) a4 a5)) (k1 (fld0$0 a3) (fld0$1 a3) a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 (Adt0 Int))(_$ Int)(a3 (Adt0 Int))(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Bool)(a6 Int)(_$ Int)) (=> (and (>= a0 0) (k0 a1 (fld0$0 a2) (fld0$1 a2) a0) (k1 (fld0$0 a2) (fld0$1 a2) a0) (k2 (fld0$1 a2) a0) (=> (< (fld0$0 a2) (fld0$1 a2)) (= (fld0$0 a3) (+ (fld0$0 a2) 1))) (=> (not (< (fld0$0 a2) (fld0$1 a2))) (= (fld0$0 a3) (fld0$0 a2))) (= (fld0$1 a3) (fld0$1 a2)) (= (mkadt1$0 (< (fld0$0 a2) (fld0$1 a2))) (mkadt1$0 true)) (= a4 (fld0$0 a2)) (k3 a6 a0 a1 (fld0$0 a2) (fld0$1 a2) (fld0$0 a3) (fld0$1 a3) a4 a5)) (k2 (fld0$1 a3) a0))))

(check-sat)
