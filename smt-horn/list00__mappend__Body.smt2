(set-logic HORN)

;; Tag 0: Ret at 70:1: 70:2 (ESpan { span: tests/pos/enums/list00.rs:64:65: 64:70 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$1) 0) (>= (fld0$0 reftgen$n2$2) 0) (= reftgen$n1$1 (mkadt0$0 0))) (k0 (fld0$0 reftgen$n2$2) (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)))))
(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(_$ Int)(_$ Int)(a0 Adt0)(_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$1) 0) (>= (fld0$0 reftgen$n2$2) 0) (= reftgen$n1$1 (mkadt0$0 (+ (fld0$0 a0) 1))) (>= (fld0$0 a0) 0) (>= (+ (fld0$0 a0) (fld0$0 reftgen$n2$2)) 0)) (k0 (+ (+ (fld0$0 a0) (fld0$0 reftgen$n2$2)) 1) (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)))))
(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n1$1) 0) (>= (fld0$0 reftgen$n2$2) 0) (k0 (fld0$0 a2) (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)) (not (= (fld0$0 a2) (+ (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2))))) false)))

(check-sat)
