(set-logic HORN)

;; Tag 0: Ret at 62:1: 62:2 (ESpan { span: tests/pos/enums/list00.rs:56:46: 56:51 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n1$0 Adt0)(reftgen$n2$1 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$0) 0) (>= (fld0$0 reftgen$n2$1) 0) (= reftgen$n1$0 (mkadt0$0 0))) (k0 (fld0$0 reftgen$n2$1) (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1)))))
(assert (forall ((reftgen$n1$0 Adt0)(reftgen$n2$1 Adt0)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$0) 0) (>= (fld0$0 reftgen$n2$1) 0) (= reftgen$n1$0 (mkadt0$0 (+ (fld0$0 a0) 1))) (>= (fld0$0 a0) 0) (>= (+ (fld0$0 a0) (fld0$0 reftgen$n2$1)) 0)) (k1 (+ (fld0$0 a0) (fld0$0 reftgen$n2$1)) (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1) (fld0$0 a0) a1))))
(assert (forall ((reftgen$n1$0 Adt0)(reftgen$n2$1 Adt0)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$0) 0) (>= (fld0$0 reftgen$n2$1) 0) (= reftgen$n1$0 (mkadt0$0 (+ (fld0$0 a0) 1))) (>= (fld0$0 a0) 0) (>= (+ (fld0$0 a0) (fld0$0 reftgen$n2$1)) 0) (k1 (fld0$0 a2) (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1) (fld0$0 a0) a1) (>= (fld0$0 a2) 0)) (k0 (+ (fld0$0 a2) 1) (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1)))))
(assert (forall ((reftgen$n1$0 Adt0)(reftgen$n2$1 Adt0)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$0) 0) (>= (fld0$0 reftgen$n2$1) 0) (k0 (fld0$0 a3) (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1)) (not (= (fld0$0 a3) (+ (fld0$0 reftgen$n1$0) (fld0$0 reftgen$n2$1))))) false)))

(check-sat)
