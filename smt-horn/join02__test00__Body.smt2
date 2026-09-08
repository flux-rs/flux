(set-logic HORN)

;; Tag 0: Ret at 4:5: 4:14 (ESpan { span: tests/pos/surface/join02.rs:1:32: 1:38 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 1 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k0 0 true))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)) (=> (and (k0 a1 a0) (not (>= (+ 0 a1) 0))) false)))

(check-sat)
