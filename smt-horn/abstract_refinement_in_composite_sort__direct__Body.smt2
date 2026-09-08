(set-logic HORN)

;; Tag 0: Ret at 19:5: 19:33 (ESpan { span: tests/pos/surface/abstract_refinement_in_composite_sort.rs:17:34: 17:40 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (>= a0 0))) false)))
(assert (forall ((a0 Int)(_$ Int)) (=> (>= a0 0) (k0 a0))))

(check-sat)
