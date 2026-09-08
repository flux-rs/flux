(set-logic HORN)

;; Tag 0: Ret at 6:5: 6:12 (ESpan { span: tests/pos/array/array02.rs:1:28: 1:34 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (=> true (k0 0)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= a0 0))) false)))

(check-sat)
