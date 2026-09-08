(set-logic HORN)

;; Tag 0: Ret at 86:23: 86:29 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:84:33: 84:37 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 reftgen$n$0) (>= a0 0)) (k1 10 a0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 a1) (< a1 reftgen$n$0)) (k0 a1 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 a1) (< a1 reftgen$n$0) (k1 a2 a1 reftgen$n$0)) (k2 a2 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (<= 0 reftgen$n$0) (k2 a3 reftgen$n$0) (not (<= 0 a3))) false)))

(check-sat)
