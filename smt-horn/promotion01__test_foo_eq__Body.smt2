(set-logic HORN)

;; Tag 0: Ret at 19:22: 19:31 (ESpan { span: tests/with_deps/pos/surface/promotion01.rs:17:30: 17:34 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0) (mkadt0$1))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Adt0) Bool)
(declare-fun k2 (Int) Bool)
(declare-fun k3 (Adt0) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (=> true (k1 mkadt0$0)))
(assert (forall ((a1 Int)) (=> (= a1 0) (k2 a1))))
(assert (=> true (k3 mkadt0$0)))
(assert (forall ((a2 Int)(_$ Int)(a3 Adt0)(_$ Int)(a4 Int)(_$ Int)(a5 Adt0)(_$ Int)) (=> (and (= a2 0) (k2 a2) (k3 a3) (= a4 0) (k0 a4) (k1 a5) (not (= (= a3 a5) true))) false)))

(check-sat)
