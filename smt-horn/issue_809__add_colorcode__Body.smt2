(set-logic HORN)

;; Tag 0: Ret at 15:13: 21:6 (ESpan { span: tests/pos/surface/issue-809.rs:13:44: 13:50 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int) Bool)
(declare-fun k3 (Int Int) Bool)

(assert (forall ((reftgen$c$0 Adt0)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 reftgen$c$0)) (>= a0 0) (= reftgen$c$0 (mkadt0$0 1))) (k1 (+ a0 1) a0 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 reftgen$c$0)) (>= a0 0) (= reftgen$c$0 (mkadt0$0 2))) (k1 (+ a0 2) a0 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 (fld0$0 reftgen$c$0)) (>= a0 0) (= reftgen$c$0 (mkadt0$0 3))) (k1 (+ a0 3) a0 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a1 Int)(_$ Int)) (=> (k2 a1 (fld0$0 reftgen$c$0)) (k0 a1 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k2 a1 (fld0$0 reftgen$c$0)) (k1 a2 a1 (fld0$0 reftgen$c$0))) (k3 a2 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a3 Int)) (=> true (k2 a3 (fld0$0 reftgen$c$0)))))
(assert (forall ((reftgen$c$0 Adt0)(a4 Int)(_$ Int)) (=> (and (k3 a4 (fld0$0 reftgen$c$0)) (not (>= a4 (fld0$0 reftgen$c$0)))) false)))

(check-sat)
