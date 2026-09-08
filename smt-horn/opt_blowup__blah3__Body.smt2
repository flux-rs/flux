(set-logic HORN)

;; Tag 0: Ret at 106:5: 106:14 (ESpan { span: tests/pos/surface/opt_blowup.rs:93:36: 93:41 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int) Bool)
(declare-fun k3 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)) (=> (< reftgen$n$0 a0) (k0 a0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (< a1 a2)) (k1 a2 reftgen$n$0 a1))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (k1 a3 reftgen$n$0 a1) (< a3 a4)) (k2 a4 reftgen$n$0 a1 a3))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (k1 a3 reftgen$n$0 a1) (k2 a5 reftgen$n$0 a1 a3)) (k3 a5 reftgen$n$0 a1 a3 a5))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)(a6 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (k1 a3 reftgen$n$0 a1) (k2 a5 reftgen$n$0 a1 a3) (k3 a6 reftgen$n$0 a1 a3 a5) (not (< reftgen$n$0 a6))) false)))

(check-sat)
