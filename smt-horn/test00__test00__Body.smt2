(set-logic HORN)

;; Tag 0: Ret at 13:5: 13:15 (ESpan { span: tests/pos/abstract_refinements/test00.rs:11:28: 11:38 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 4)))
(assert (=> true (k0 10)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (>= a0 4) (>= a0 10) (not (= (mod a0 2) 0))) false)))

(check-sat)
