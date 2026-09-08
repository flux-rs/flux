(set-logic HORN)

;; Tag 0: Ret at 14:5: 14:24 (ESpan { span: tests/pos/array/array00.rs:11:29: 11:35 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 10)))
(assert (=> true (k0 20)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (k0 a0) (k0 a1) (not (> (+ a0 a1) 10))) false)))

(check-sat)
