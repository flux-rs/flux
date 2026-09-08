(set-logic HORN)

;; Tag 0: Ret at 23:1: 23:2 (ESpan { span: tests/pos/enums/opt01.rs:17:36: 17:37 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Bool Bool Bool) Bool)
;; orig: $k0
(declare-fun k1 (Bool Bool) Bool)

(assert (forall ((reftgen$b$0 Adt0)(_$ Int)) (=> (= reftgen$b$0 (mkadt0$0 false)) (k0 false false (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)) (=> (= reftgen$b$0 (mkadt0$0 false)) (k1 false (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)(a0 Int)) (=> (= reftgen$b$0 (mkadt0$0 true)) (k0 true true (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)(a0 Int)) (=> (= reftgen$b$0 (mkadt0$0 true)) (k1 true (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(a1 Bool)(a2 Bool)(_$ Int)) (=> (and (k0 a1 a2 (fld0$0 reftgen$b$0)) (k1 a2 (fld0$0 reftgen$b$0)) (not (= a2 (fld0$0 reftgen$b$0)))) false)))

(check-sat)
