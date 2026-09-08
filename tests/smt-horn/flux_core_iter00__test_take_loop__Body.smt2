(set-logic HORN)

;; Tag 0: Underflow at 44:19: 44:40
;; Tag 1: Assert("possible out-of-bounds access") at 49:9: 49:23

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Int) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
;; alias reft: <(<I as IntoIterator>::IntoIter) as Iterator>::step
(declare-fun c0 (Int Int) Bool)
;; alias reft: <(<I as IntoIterator>::IntoIter) as Iterator>::done
(declare-fun c1 (Int) Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k2 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0) (not (>= (- reftgen$len$0 reftgen$n$1) 0))) false)))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0)) (k0 reftgen$n$1 (- reftgen$len$0 reftgen$n$1) a1 reftgen$len$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0)) (k1 (- reftgen$len$0 reftgen$n$1) a1 reftgen$len$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0)) (k2 a1 reftgen$len$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0) (k0 a2 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k2 (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (not (< a2 reftgen$len$0))) false)))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0) (k0 a2 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k2 (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 reftgen$len$0)) (k0 (+ a2 1) (fld0$0 a4) (fld0$1 a4) reftgen$len$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0) (k0 a2 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k2 (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 reftgen$len$0)) (k1 (fld0$0 a4) (fld0$1 a4) reftgen$len$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$len$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(a2 Int)(a3 (Adt0 Int))(_$ Int)(a4 (Adt0 Int))(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (>= reftgen$len$0 0) (<= reftgen$n$1 reftgen$len$0) (>= reftgen$n$1 0) (k0 a2 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k1 (fld0$0 a3) (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (k2 (fld0$1 a3) reftgen$len$0 reftgen$n$1 a0 a1) (ite (> (fld0$0 a3) 0) (and (= (fld0$0 a4) (- (fld0$0 a3) 1)) (c0 (fld0$1 a3) (fld0$1 a4))) (and (= (fld0$0 a4) (fld0$0 a3)) (= (fld0$1 a4) (fld0$1 a3)))) (= (mkadt1$0 (not (or (<= (fld0$0 a3) 0) (c1 (fld0$1 a3))))) (mkadt1$0 true)) (< a2 reftgen$len$0)) (k2 (fld0$1 a4) reftgen$len$0 reftgen$n$1 a0 a1))))

(check-sat)
