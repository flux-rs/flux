(set-logic HORN)

;; Tag 0: Ret at 5:5: 5:8 (ESpan { span: tests/pos/surface/slice00.rs:1:48: 1:54 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (> a2 0)) (k0 a2 a0 a1))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(a3 Int)(a4 Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a3 0) (>= a4 0) (k0 a5 a0 a1) (not (>= a5 0))) false)))

(check-sat)
