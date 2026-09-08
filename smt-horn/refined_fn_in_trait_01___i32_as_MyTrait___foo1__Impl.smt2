(set-logic HORN)

;; Tag 0: Subtype(Output) at 11:5: 11:27 (ESpan { span: tests/pos/surface/refined_fn_in_trait_01.rs:2:68: 2:72 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int (Array Int Bool) Int) Bool)

(assert (forall ((reftgen$p$0 (Array Int Bool))(a0 Int)(_$ Int)) (=> (reftgen$p$0 a0) (k0 a0 reftgen$p$0 a0))))
(assert (forall ((reftgen$p$0 (Array Int Bool))(a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (reftgen$p$0 a0) (k0 a1 reftgen$p$0 a0) (not (reftgen$p$0 a1))) false)))

(check-sat)
