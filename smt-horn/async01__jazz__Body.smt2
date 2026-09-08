(set-logic HORN)

;; Tag 0: Call at 20:18: 20:28 (ESpan { span: tests/pos/surface/async01.rs:9:54: 9:60 (#0), base: None })
;; Tag 1: Ret at 21:5: 21:11 (ESpan { span: tests/pos/surface/async01.rs:17:39: 17:43 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)) (=> (<= 0 reftgen$k$0) (k0 a1 reftgen$k$0 a0 a1))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)(a2 Int)(_$ Int)(a3 Int)(a4 Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a2 reftgen$k$0 a0 a1) (<= reftgen$k$0 a4) (not (<= 0 a4))) false)))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)(a2 Int)(_$ Int)(a3 Int)(a4 Int)(_$ Int)(a5 Int)(a6 Int)) (=> (and (<= 0 reftgen$k$0) (k0 a2 reftgen$k$0 a0 a1) (<= reftgen$k$0 a4)) (k1 a6 reftgen$k$0 a0 a1 a2 a3 a4 a5 a6))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)(a2 Int)(_$ Int)(a3 Int)(a4 Int)(_$ Int)(a5 Int)(a6 Int)(a7 Int)(_$ Int)(a8 Int)(a9 Int)(_$ Int)) (=> (and (<= 0 reftgen$k$0) (k0 a2 reftgen$k$0 a0 a1) (<= reftgen$k$0 a4) (k1 a7 reftgen$k$0 a0 a1 a2 a3 a4 a5 a6) (<= a4 a9) (not (<= reftgen$k$0 a9))) false)))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)(a2 Int)(_$ Int)(a3 Int)(a4 Int)(_$ Int)(a5 Int)(a6 Int)(a7 Int)(_$ Int)(a8 Int)) (=> (and (<= 0 reftgen$k$0) (k0 a2 reftgen$k$0 a0 a1) (<= reftgen$k$0 a4) (k1 a7 reftgen$k$0 a0 a1 a2 a3 a4 a5 a6)) (k1 a8 reftgen$k$0 a0 a1 a2 a3 a4 a5 a6))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(a0 Int)(a1 Int)(a2 Int)(_$ Int)(a3 Int)) (=> (and (<= 0 reftgen$k$0) (k0 a2 reftgen$k$0 a0 a1)) (k0 a3 reftgen$k$0 a0 a1))))

(check-sat)
