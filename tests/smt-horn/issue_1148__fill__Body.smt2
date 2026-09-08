(set-logic HORN)

;; Tag 0: Ret at 28:5: 31:6 (ESpan { span: tests/with_deps/pos/surface/issue-1148.rs:25:79: 25:80 (#0), base: None })
;; Tag 1: Call at 29:9: 29:26 (ESpan { span: tests/with_deps/pos/surface/issue-1148.rs:17:21: 17:32 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$1 Int)(_$ Int)) (=> (>= reftgen$n$1 0) (k0 0 0 reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)(_$ Int)) (=> (>= reftgen$n$1 0) (k1 0 reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$1 0) (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) (not (< a0 reftgen$n$1)) (not (= a1 reftgen$n$1))) false)))
(assert (forall ((reftgen$n$1 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)) (=> (and (>= reftgen$n$1 0) (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) (< a0 reftgen$n$1) (not (< a1 reftgen$n$1))) false)))
(assert (forall ((reftgen$n$1 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)) (=> (and (>= reftgen$n$1 0) (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) (< a0 reftgen$n$1)) (k0 (+ a0 1) (+ a1 1) reftgen$n$1))))
(assert (forall ((reftgen$n$1 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)) (=> (and (>= reftgen$n$1 0) (k0 a0 a1 reftgen$n$1) (k1 a1 reftgen$n$1) (< a0 reftgen$n$1)) (k1 (+ a1 1) reftgen$n$1))))

(check-sat)
