(set-logic HORN)

;; Tag 0: Ret at 14:5: 14:6 (ESpan { span: tests/pos/surface/loop00.rs:6:39: 6:40 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Bool) Bool)
(declare-fun k2 (Int Int Int Bool) Bool)

(assert (forall ((reftgen$k$0 Int)(_$ Int)) (=> (<= 0 reftgen$k$0) (k0 reftgen$k$0 reftgen$k$0))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) (not a1)) (k1 reftgen$k$0 a0 a1))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) a1 (not (< a0 (- 2147483647 1)))) (k1 reftgen$k$0 a0 true))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) a1 (< a0 (- 2147483647 1))) (k0 (+ a0 1) reftgen$k$0))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) (k1 reftgen$k$0 a0 a1)) (k2 a0 reftgen$k$0 a0 a1))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) (k1 reftgen$k$0 a0 a1) (k2 a2 reftgen$k$0 a0 a1) (not (> a2 0)) (not (= a2 0))) false)))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(_$ Int)(a1 Bool)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a0 reftgen$k$0) (k1 reftgen$k$0 a0 a1) (k2 a2 reftgen$k$0 a0 a1) (> a2 0)) (k2 (- a2 1) reftgen$k$0 a0 a1))))

(check-sat)
