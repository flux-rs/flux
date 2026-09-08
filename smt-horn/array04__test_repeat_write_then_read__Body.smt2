(set-logic HORN)

;; Tag 0: Ret at 23:5: 23:11 (ESpan { span: tests/pos/array/array04.rs:19:25: 19:32 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 42)))
(assert (forall ((_$ Int)) (=> true (k0 100))))
(assert (forall ((_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (k0 a0) (not (>= a0 42))) false)))

(check-sat)
