(set-logic HORN)

;; Tag 0: Ret at 10:5: 10:8 (ESpan { span: tests/pos/structs/struct03.rs:6:44: 6:50 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (> a0 0) (k0 (- a0 1) a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (> a0 0) (k0 a1 a0) (not (>= a1 0))) false)))

(check-sat)
