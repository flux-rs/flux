(set-logic HORN)

;; Tag 0: Ret at 13:5: 13:10 (ESpan { span: tests/pos/structs/enum-join.rs:6:50: 6:55 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k0 a0))))
(assert (forall ((a1 Bool)(a2 Int)(_$ Int)) (=> (>= a2 0) (k0 a2))))
(assert (forall ((a3 Int)(_$ Int)) (=> (and (k0 a3) (not (> (+ a3 1) 0))) false)))

(check-sat)
