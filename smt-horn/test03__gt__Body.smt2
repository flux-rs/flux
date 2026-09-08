(set-logic HORN)

;; Tag 0: Ret at 7:5: 7:6 (ESpan { span: tests/pos/abstract_refinements/test03.rs:5:33: 5:38 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$x$0 Int)(a0 Int)(_$ Int)) (=> (and (k0 a0 reftgen$x$0) (not (> a0 reftgen$x$0))) false)))
(assert (forall ((reftgen$x$0 Int)(a0 Int)(_$ Int)) (=> (> a0 reftgen$x$0) (k0 a0 reftgen$x$0))))

(check-sat)
