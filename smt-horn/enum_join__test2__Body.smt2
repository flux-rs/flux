(set-logic HORN)

;; Tag 0: Ret at 25:1: 25:2 (ESpan { span: tests/pos/structs/enum-join.rs:16:59: 16:65 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (forall ((a1 Bool)(a2 Int)) (=> (= a2 0) (k0 a2))))
(assert (forall ((a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (= a3 0) (k0 a3) (>= a4 0)) (k1 a4))))
(assert (forall ((a3 Int)(_$ Int)) (=> (and (= a3 0) (k0 a3)) (k1 0))))
(assert (forall ((a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= a3 0) (k0 a3) (k1 a5) (not (>= a5 0))) false)))

(check-sat)
