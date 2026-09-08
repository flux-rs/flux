(set-logic HORN)

;; Tag 0: Underflow at 29:15: 29:20
;; Tag 1: Call at 30:13: 30:27 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:47: 35:52 (#0), base: None })
;; Tag 2: Call at 30:13: 30:27 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:64: 35:69 (#0), base: None })
;; Tag 3: Call at 34:25: 34:39 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:64: 35:69 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k2
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int Bool) Bool)
;; orig: $k1
(declare-fun k2 (Int Int Int Int Bool) Bool)

(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0)) (k0 1 reftgen$m$0 reftgen$n$1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (not (>= (- reftgen$n$1 1) 0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not (< 0 reftgen$m$0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not (< a0 reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not a1)) (k1 reftgen$m$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) a1) (k2 (+ 0 1) reftgen$m$0 reftgen$n$1 a0 true))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)(a2 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) a1 (k2 a2 reftgen$m$0 reftgen$n$1 a0 true) (< a2 reftgen$m$0) (not (< a0 reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(a3 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) a1 (k2 a2 reftgen$m$0 reftgen$n$1 a0 true) (< a2 reftgen$m$0) (not a3)) (k1 reftgen$m$0 reftgen$n$1 a0 true))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(a3 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) a1 (k2 a2 reftgen$m$0 reftgen$n$1 a0 true) (< a2 reftgen$m$0) a3) (k2 (+ a2 1) reftgen$m$0 reftgen$n$1 a0 true))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (k1 reftgen$m$0 reftgen$n$1 a0 a1)) (k0 (+ a0 1) reftgen$m$0 reftgen$n$1))))

(check-sat)
