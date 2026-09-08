(set-logic HORN)

;; Tag 0: Ret at 11:15: 11:17 (ESpan { span: tests/with_deps/pos/surface/promotion00.rs:9:30: 9:34 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)
(declare-fun k3 (Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (=> true (k1 0)))
(assert (forall ((a1 Int)) (=> (= a1 0) (k2 a1))))
(assert (=> true (k3 0)))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= a2 0) (k2 a2) (k3 a3) (= a4 0) (k0 a4) (k1 a5) (not (= (= a3 a5) true))) false)))

(check-sat)
