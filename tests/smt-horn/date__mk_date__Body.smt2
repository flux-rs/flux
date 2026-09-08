(set-logic HORN)

;; Tag 0: Call at 50:29: 50:54 (ESpan { span: tests/pos/surface/date.rs:5:63: 5:87 (#0), base: Some(tests/pos/surface/date.rs:18:32: 18:46 (#0)) })
;; Tag 1: Call at 50:29: 50:54 (ESpan { span: tests/pos/surface/date.rs:8:58: 8:84 (#0), base: Some(tests/pos/surface/date.rs:20:32: 20:48 (#0)) })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (not (or (or (or (= a1 4) (= a1 6)) (= a1 9)) (= a1 11)))) (k0 a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (or (or (or (= a1 4) (= a1 6)) (= a1 9)) (= a1 11)) (<= a0 30)) (k0 a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (k0 a0 a1 a2) (not (not (= a1 2))) (<= a0 29) (=> (= a0 29) (or (= (mod a2 400) 0) (and (= (mod a2 4) 0) (> (mod a2 100) 0))))) (k1 a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (k0 a0 a1 a2) (not (= a1 2))) (k1 a0 a1 a2))))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (k0 a0 a1 a2) (k1 a0 a1 a2) (not (=> (or (or (or (= a1 4) (= a1 6)) (= a1 9)) (= a1 11)) (<= a0 30)))) false)))
(assert (forall ((a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (>= a1 0) (>= a2 0) (<= 1 a2) (<= 1 a1) (<= a1 12) (<= 1 a0) (<= a0 31) (k0 a0 a1 a2) (k1 a0 a1 a2) (not (=> (= a1 2) (and (<= a0 29) (=> (= a0 29) (or (= (mod a2 400) 0) (and (= (mod a2 4) 0) (> (mod a2 100) 0)))))))) false)))

(check-sat)
