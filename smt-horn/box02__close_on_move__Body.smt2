(set-logic HORN)

;; Tag 0: Fold at 54:20: 54:21 (ESpan { span: tests/pos/surface/box02.rs:45:27: 45:32 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= a1 0) (k0 a1) (> a2 0) (not (> (+ a2 1) 0))) false)))

(check-sat)
