(set-logic HORN)

;; Tag 0: Ret at 19:9: 19:19

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$s$0 Adt0)) (=> true (k0 (fld0$0 reftgen$s$0) (fld0$0 reftgen$s$0)))))
(assert (forall ((reftgen$s$0 Adt0)(a0 Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 reftgen$s$0)) (not (= a0 (fld0$0 reftgen$s$0)))) false)))

(check-sat)
