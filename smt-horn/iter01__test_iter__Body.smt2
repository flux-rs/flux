(set-logic HORN)

;; Tag 0: Call at 11:9: 11:25 (ESpan { span: tests/pos/surface/iter01.rs:5:21: 5:25 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)
(declare-fun k2 (Int) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (<= 0 a1) (k1 a1))))
(assert (forall ((a2 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= a2 0) (k0 a2) (k1 a3)) (k2 a3))))
(assert (forall ((a2 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (= a2 0) (k0 a2) (k2 a4) (not (= (<= 0 a4) true))) false)))
(assert (forall ((a2 Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= a2 0) (k0 a2) (k2 a4) (k2 a5)) (k1 a5))))

(check-sat)
