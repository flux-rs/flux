(set-logic HORN)

;; Tag 0: Ret at 23:5: 23:6 (ESpan { span: tests/pos/surface/refined_fn_in_trait_01.rs:21:54: 21:58 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int (Array Int Bool) Int) Bool)

(assert (forall ((reftgen$q$0 (Array Int Bool))(a0 Int)(_$ Int)) (=> (reftgen$q$0 a0) (k0 a0 reftgen$q$0 a0))))
(assert (forall ((reftgen$q$0 (Array Int Bool))(a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (reftgen$q$0 a0) (k0 a1 reftgen$q$0 a0) (not (reftgen$q$0 a1))) false)))

(check-sat)
