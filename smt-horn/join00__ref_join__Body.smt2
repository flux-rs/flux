(set-logic HORN)

;; Tag 0: Call at 16:5: 16:19 (ESpan { span: tests/pos/surface/join00.rs:1:21: 1:25 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 2 a0))))
(assert (forall ((a0 Bool)(_$ Int)) (=> a0 (k0 1 true))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)) (=> (and (k0 a1 a0) (not (= (> a1 0) true))) false)))

(check-sat)
