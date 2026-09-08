(set-logic HORN)

;; Tag 0: Underflow at 12:15: 12:20
;; Tag 1: Call at 13:13: 13:27 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:47: 35:52 (#0), base: None })
;; Tag 2: Call at 13:13: 13:27 (ESpan { span: tests/pos/surface/../../lib/rmat.rs:35:64: 35:69 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0)) (k0 1 reftgen$m$0 reftgen$n$1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (not (>= (- reftgen$n$1 1) 0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not (< 0 reftgen$m$0))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not (< a0 reftgen$n$1))) false)))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (> reftgen$m$0 0) (>= reftgen$m$0 0) (> reftgen$n$1 0) (>= reftgen$n$1 0) (k0 a0 reftgen$m$0 reftgen$n$1) (< a0 (- reftgen$n$1 1)) (not a1)) (k0 (+ a0 1) reftgen$m$0 reftgen$n$1))))

(check-sat)
