(set-logic HORN)

;; Tag 0: Call at 57:18: 57:32 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:47: 35:52 (#0), base: None })
;; Tag 1: Call at 57:18: 57:32 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:64: 35:69 (#0), base: None })
;; Tag 2: Underflow at 60:16: 60:21
;; Tag 3: Ret at 69:5: 69:6 (ESpan { span: tests/pos/surface/simplex.rs:55:79: 55:84 (#0), base: None })
;; Tag 4: Ret at 69:5: 69:6 (ESpan { span: tests/pos/surface/simplex.rs:55:88: 55:95 (#0), base: None })
;; Tag 5: Call at 62:19: 62:34 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:47: 35:52 (#0), base: None })
;; Tag 6: Call at 62:19: 62:34 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:64: 35:69 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int Int Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k0
(declare-fun k2 (Int Int Int Int Int Bool) Bool)

(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (not (< 0 reftgen$m$0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (not (< 1 reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0)) (k0 1 2 reftgen$m$0 reftgen$n$1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0)) (k1 2 reftgen$m$0 reftgen$n$1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (not (>= (- reftgen$n$1 1) 0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (not (< a1 (- reftgen$n$1 1))) (not (< 0 a0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (not (< a1 (- reftgen$n$1 1))) (not (< (+ a0 1) reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) (not (< 0 reftgen$m$0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) (not (< a1 reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) (not a2)) (k2 a0 reftgen$m$0 reftgen$n$1 a0 a1 a2))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) a2) (k2 a1 reftgen$m$0 reftgen$n$1 a0 a1 true))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(a3 Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) (k2 a3 reftgen$m$0 reftgen$n$1 a0 a1 a2)) (k0 a3 (+ a1 1) reftgen$m$0 reftgen$n$1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(a3 Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 2) (>= reftgen$n$1 0) (k0 a0 a1 reftgen$m$0 reftgen$n$1) (k1 a1 reftgen$m$0 reftgen$n$1) (< a1 (- reftgen$n$1 1)) (k2 a3 reftgen$m$0 reftgen$n$1 a0 a1 a2)) (k1 (+ a1 1) reftgen$m$0 reftgen$n$1))))

(check-sat)
