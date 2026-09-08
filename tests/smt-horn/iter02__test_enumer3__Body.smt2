(set-logic HORN)

;; Tag 0: Call at 52:9: 52:34 (ESpan { span: tests/with_deps/pos/surface/iter02.rs:9:21: 9:25 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)(Adt2 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Int) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Int) (fld1$1 Int)))((mkadt2$0 (fld2$0 Bool)))))
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

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k0 0 0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k1 0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k2 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Adt1))(_$ Int)(a1 (Adt0 Adt1))(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 (fld0$0 a0) (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k1 (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k2 (fld1$1 (fld0$1 a0)) reftgen$n$0) (= (+ (fld0$0 a0) 1) (fld0$0 a1)) (= (fld1$1 (fld0$1 a0)) (fld1$1 (fld0$1 a1))) (ite (< (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))) (= (fld1$0 (fld0$1 a1)) (+ (fld1$0 (fld0$1 a0)) 1)) (= (fld1$0 (fld0$1 a1)) (fld1$0 (fld0$1 a0)))) (= (mkadt2$0 (not (>= (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))))) (mkadt2$0 true)) (>= (fld0$0 a0) 0) (>= a2 0) (not (= (< (fld0$0 a0) reftgen$n$0) true))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Adt1))(_$ Int)(a1 (Adt0 Adt1))(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 (fld0$0 a0) (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k1 (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k2 (fld1$1 (fld0$1 a0)) reftgen$n$0) (= (+ (fld0$0 a0) 1) (fld0$0 a1)) (= (fld1$1 (fld0$1 a0)) (fld1$1 (fld0$1 a1))) (ite (< (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))) (= (fld1$0 (fld0$1 a1)) (+ (fld1$0 (fld0$1 a0)) 1)) (= (fld1$0 (fld0$1 a1)) (fld1$0 (fld0$1 a0)))) (= (mkadt2$0 (not (>= (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))))) (mkadt2$0 true)) (>= (fld0$0 a0) 0) (>= a2 0)) (k0 (fld0$0 a1) (fld1$0 (fld0$1 a1)) (fld1$1 (fld0$1 a1)) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Adt1))(_$ Int)(a1 (Adt0 Adt1))(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 (fld0$0 a0) (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k1 (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k2 (fld1$1 (fld0$1 a0)) reftgen$n$0) (= (+ (fld0$0 a0) 1) (fld0$0 a1)) (= (fld1$1 (fld0$1 a0)) (fld1$1 (fld0$1 a1))) (ite (< (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))) (= (fld1$0 (fld0$1 a1)) (+ (fld1$0 (fld0$1 a0)) 1)) (= (fld1$0 (fld0$1 a1)) (fld1$0 (fld0$1 a0)))) (= (mkadt2$0 (not (>= (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))))) (mkadt2$0 true)) (>= (fld0$0 a0) 0) (>= a2 0)) (k1 (fld1$0 (fld0$1 a1)) (fld1$1 (fld0$1 a1)) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Adt1))(_$ Int)(a1 (Adt0 Adt1))(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 (fld0$0 a0) (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k1 (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0)) reftgen$n$0) (k2 (fld1$1 (fld0$1 a0)) reftgen$n$0) (= (+ (fld0$0 a0) 1) (fld0$0 a1)) (= (fld1$1 (fld0$1 a0)) (fld1$1 (fld0$1 a1))) (ite (< (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))) (= (fld1$0 (fld0$1 a1)) (+ (fld1$0 (fld0$1 a0)) 1)) (= (fld1$0 (fld0$1 a1)) (fld1$0 (fld0$1 a0)))) (= (mkadt2$0 (not (>= (fld1$0 (fld0$1 a0)) (fld1$1 (fld0$1 a0))))) (mkadt2$0 true)) (>= (fld0$0 a0) 0) (>= a2 0)) (k2 (fld1$1 (fld0$1 a1)) reftgen$n$0))))

(check-sat)
