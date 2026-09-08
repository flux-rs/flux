(set-logic HORN)

;; Tag 0: Call at 16:5: 16:17 (ESpan { span: tests/pos/abstract_refinements/test04.rs:20:23: 20:29 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 (+ a0 1) a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (k1 a1 a0) (not (>= a1 0))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (>= a1 0)) (k1 a1 a0))))

(check-sat)
