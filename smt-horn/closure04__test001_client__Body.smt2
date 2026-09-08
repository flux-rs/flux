(set-logic HORN)

;; Tag 0: Subtype(Output) at 10:5: 10:19 (ESpan { span: tests/pos/surface/closure04.rs:1:81: 1:87 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (<= 0 a1) (k0 a1))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 a1) (k1 a2 a1) (not (<= 0 a2))) false)))

(check-sat)
