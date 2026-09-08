(set-logic HORN)

;; Tag 0: Fold at 71:5: 71:6 (ESpan { span: tests/pos/surface/too_many_linked_lists.rs:5:19: 5:27 (#0), base: None })
;; Tag 1: Ret at 71:5: 71:6 (ESpan { span: tests/pos/surface/too_many_linked_lists.rs:60:45: 60:50 (#0), base: None })
;; Tag 2: Ret at 71:5: 71:6

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)(Adt2 0)) (((mkadt0$0 (fld0$0 Int)))((mkadt1$0 (fld1$0 Int)))((mkadt2$0 (fld2$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Bool Int Int) Bool)
(declare-fun k2 (Int Int) Bool)

(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(a0 Int)) (=> (>= (fld0$0 reftgen$n$1) 0) (k0 a0 (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (= (mkadt1$0 (fld0$0 reftgen$n$1)) (mkadt1$0 0))) (k1 false 0 (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (= (mkadt1$0 (fld0$0 reftgen$n$1)) (mkadt1$0 0))) (k2 0 (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a1 Adt2)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (= (mkadt1$0 (fld0$0 reftgen$n$1)) (mkadt1$0 (+ (fld2$0 a1) 1))) (>= (fld2$0 a1) 0) (k0 a2 (fld0$0 reftgen$n$1))) (k1 true (fld2$0 a1) (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a1 Adt2)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (= (mkadt1$0 (fld0$0 reftgen$n$1)) (mkadt1$0 (+ (fld2$0 a1) 1))) (>= (fld2$0 a1) 0) (k0 a2 (fld0$0 reftgen$n$1))) (k2 (fld2$0 a1) (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Bool)(a4 Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (k1 a3 a4 (fld0$0 reftgen$n$1)) (k2 a4 (fld0$0 reftgen$n$1)) (not (>= a4 0))) false)))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Bool)(a4 Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (k1 a3 a4 (fld0$0 reftgen$n$1)) (k2 a4 (fld0$0 reftgen$n$1)) (not (= a3 (> (fld0$0 reftgen$n$1) 0)))) false)))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Bool)(a4 Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (k1 a3 a4 (fld0$0 reftgen$n$1)) (k2 a4 (fld0$0 reftgen$n$1)) (not (= a4 (fld0$0 (ite (> (fld0$0 reftgen$n$1) 0) (mkadt0$0 (- (fld0$0 reftgen$n$1) 1)) reftgen$n$1))))) false)))

(check-sat)
