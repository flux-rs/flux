(set-logic HORN)

;; Tag 0: Underflow at 17:27: 17:35
;; Tag 1: Underflow at 22:29: 22:41
;; Tag 2: Call at 23:28: 23:36 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:181:44: 181:49 (#0), base: None })
;; Tag 3: Underflow at 31:13: 31:30

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int Int) Bool)
(declare-fun k3 (Int Int Int Int Int Int) Bool)
(declare-fun k4 (Int Int Int Int Int Int Int) Bool)

(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (not (>= (- (fld0$0 a1) 1) 0))) false)))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0))) (k0 0 (- (fld0$0 a1) 1) a0 (fld0$0 a1)))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0))) (k1 (- (fld0$0 a1) 1) a0 (fld0$0 a1)))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (not (>= (- a3 a2) 0))) false)))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3)) (k2 a4 a0 (fld0$0 a1) a2 a3))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (not (< (+ a2 (div (- a3 a2) 2)) (fld0$0 a1)))) false)))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (not (> a5 a0))) (k3 a3 a0 (fld0$0 a1) a2 a3 a5))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (> a5 a0) (not (= (+ a2 (div (- a3 a2) 2)) 0)) (not (>= (- (+ a2 (div (- a3 a2) 2)) 1) 0))) false)))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (> a5 a0) (not (= (+ a2 (div (- a3 a2) 2)) 0))) (k3 (- (+ a2 (div (- a3 a2) 2)) 1) a0 (fld0$0 a1) a2 a3 a5))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (k3 a6 a0 (fld0$0 a1) a2 a3 a5) (not (< a5 a0))) (k4 a2 a0 (fld0$0 a1) a2 a3 a5 a6))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (k3 a6 a0 (fld0$0 a1) a2 a3 a5) (< a5 a0)) (k4 (+ (+ a2 (div (- a3 a2) 2)) 1) a0 (fld0$0 a1) a2 a3 a5 a6))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (k3 a6 a0 (fld0$0 a1) a2 a3 a5) (k4 a7 a0 (fld0$0 a1) a2 a3 a5 a6)) (k0 a7 a6 a0 (fld0$0 a1)))))
(assert (forall ((a0 Int)(a1 Adt0)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(a3 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a1)) (>= (fld0$0 a1) 0) (not (<= (fld0$0 a1) 0)) (k0 a2 a3 a0 (fld0$0 a1)) (k1 a3 a0 (fld0$0 a1)) (<= a2 a3) (k2 a5 a0 (fld0$0 a1) a2 a3) (not (= a5 a0)) (k3 a6 a0 (fld0$0 a1) a2 a3 a5) (k4 a7 a0 (fld0$0 a1) a2 a3 a5 a6)) (k1 a6 a0 (fld0$0 a1)))))

(check-sat)
