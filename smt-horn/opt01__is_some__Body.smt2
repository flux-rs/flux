(set-logic HORN)

;; Tag 0: Ret at 15:1: 15:2 (ESpan { span: tests/pos/enums/opt01.rs:9:36: 9:37 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Bool Bool Bool) Bool)
(declare-fun k1 (Bool Bool) Bool)

(assert (forall ((reftgen$b$0 Adt0)(_$ Int)) (=> (= reftgen$b$0 (mkadt0$0 false)) (k0 false false (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)) (=> (= reftgen$b$0 (mkadt0$0 false)) (k1 false (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)(a0 Int)) (=> (= reftgen$b$0 (mkadt0$0 true)) (k0 true true (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(_$ Int)(a0 Int)) (=> (= reftgen$b$0 (mkadt0$0 true)) (k1 true (fld0$0 reftgen$b$0)))))
(assert (forall ((reftgen$b$0 Adt0)(a1 Bool)(a2 Bool)(_$ Int)) (=> (and (k0 a1 a2 (fld0$0 reftgen$b$0)) (k1 a2 (fld0$0 reftgen$b$0)) (not (= a2 (fld0$0 reftgen$b$0)))) false)))

(check-sat)
