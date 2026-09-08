(set-logic HORN)

;; Tag 0: Ret at 24:9: 24:12 (ESpan { span: tests/pos/enums/issue-234.rs:16:40: 16:41 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)) (=> true (k0 0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)) (=> true (k1 (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(a2 Adt0)(_$ Int)(a3 Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$0 reftgen$n$0)) (k1 (fld0$0 a1) (fld0$0 reftgen$n$0)) (= a1 (mkadt0$0 (+ (fld0$0 a2) 1)))) (k0 (+ a0 1) (fld0$0 a2) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(a2 Adt0)(_$ Int)(a3 Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$0 reftgen$n$0)) (k1 (fld0$0 a1) (fld0$0 reftgen$n$0)) (= a1 (mkadt0$0 (+ (fld0$0 a2) 1)))) (k1 (fld0$0 a2) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(a0 Int)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 a1) (fld0$0 reftgen$n$0)) (k1 (fld0$0 a1) (fld0$0 reftgen$n$0)) (= a1 (mkadt0$0 0)) (not (= a0 (fld0$0 reftgen$n$0)))) false)))

(check-sat)
