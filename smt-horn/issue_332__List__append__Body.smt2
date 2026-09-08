(set-logic HORN)

;; Tag 0: Ret at 18:5: 18:6 (ESpan { span: tests/pos/surface/issue-332.rs:12:28: 12:30 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(a0 Adt0)(_$ Int)) (=> (= reftgen$n1$1 (mkadt0$0 (+ (fld0$0 a0) 1))) (k0 (+ (fld0$0 a0) 1) (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)))))
(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(_$ Int)) (=> (= reftgen$n1$1 (mkadt0$0 0)) (k0 0 (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)))))
(assert (forall ((reftgen$n1$1 Adt0)(reftgen$n2$2 Adt0)(a1 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a1) (fld0$0 reftgen$n1$1) (fld0$0 reftgen$n2$2)) (not (= a1 reftgen$n1$1))) false)))

(check-sat)
