(set-logic HORN)

;; Tag 0: Ret at 12:5: 12:24 (ESpan { span: tests/pos/surface/issue-258.rs:10:32: 10:37 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (=> true (k0 1)))
(assert (forall ((a0 Int)) (=> (= a0 0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (k0 a1) (k2 a1))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= a2 0) (k1 a2) (k2 a3) (not (> a3 0))) false)))

(check-sat)
