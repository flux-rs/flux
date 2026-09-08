(set-logic HORN)

;; Tag 0: Assert("possible remainder with a divisor of zero") at 3:11: 3:16
;; Tag 1: Assert("possible reminder with overflow") at 3:11: 3:16
;; Tag 2: Ret at 9:5: 9:6 (ESpan { span: tests/pos/surface/gcd.rs:1:59: 1:64 (#0), base: None })
;; Tag 3: Assert("possible remainder with a divisor of zero") at 4:17: 4:22

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (> a0 0) (> a1 0)) (k0 a0 a1 a0 a1))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (> a0 0) (> a1 0)) (k1 a1 a0 a1))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (not (= a3 0)))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (= a3 0)) (not (not (and (= a3 (- 1)) (= a2 (- 2147483648)))))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (= a3 0)) (not (and (= a3 (- 1)) (= a2 (- 2147483648)))) (=> (and (>= a2 0) (>= a3 0)) (= a4 (mod a2 a3))) (not (> a4 0)) (not (> a3 0))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (= a3 0)) (not (and (= a3 (- 1)) (= a2 (- 2147483648)))) (=> (and (>= a2 0) (>= a3 0)) (= a4 (mod a2 a3))) (> a4 0) (not (not (= a3 0)))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (= a3 0)) (not (and (= a3 (- 1)) (= a2 (- 2147483648)))) (=> (and (>= a2 0) (>= a3 0)) (= a4 (mod a2 a3))) (> a4 0) (not (= a3 0)) (=> (and (>= a2 0) (>= a3 0)) (= a5 (mod a2 a3)))) (k0 a3 a5 a0 a1))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (> a0 0) (> a1 0) (k0 a2 a3 a0 a1) (k1 a3 a0 a1) (not (= a3 0)) (not (and (= a3 (- 1)) (= a2 (- 2147483648)))) (=> (and (>= a2 0) (>= a3 0)) (= a4 (mod a2 a3))) (> a4 0) (not (= a3 0)) (=> (and (>= a2 0) (>= a3 0)) (= a5 (mod a2 a3)))) (k1 a5 a0 a1))))

(check-sat)
