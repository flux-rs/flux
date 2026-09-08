(set-logic HORN)

;; Tag 0: Ret at 12:5: 12:6 (ESpan { span: tests/pos/surface/fib_loop.rs:1:43: 1:48 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (< 0 a0) (k0 a0 1 1 a0))))
(assert (forall ((a0 Int)(_$ Int)) (=> (< 0 a0) (k1 1 1 a0))))
(assert (forall ((a0 Int)(_$ Int)) (=> (< 0 a0) (k2 1 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (< 0 a0) (k0 a1 a2 a3 a0) (k1 a2 a3 a0) (k2 a3 a0) (not (> a1 2)) (not (< 0 a2))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (< 0 a0) (k0 a1 a2 a3 a0) (k1 a2 a3 a0) (k2 a3 a0) (> a1 2)) (k0 (- a1 1) (+ a2 a3) a2 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (< 0 a0) (k0 a1 a2 a3 a0) (k1 a2 a3 a0) (k2 a3 a0) (> a1 2)) (k1 (+ a2 a3) a2 a0))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (< 0 a0) (k0 a1 a2 a3 a0) (k1 a2 a3 a0) (k2 a3 a0) (> a1 2)) (k2 a2 a0))))

(check-sat)
