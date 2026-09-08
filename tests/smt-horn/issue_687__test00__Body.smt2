(set-logic HORN)

;; Tag 0: Ret at 4:34: 4:41 (ESpan { span: tests/pos/surface/issue-687.rs:1:91: 1:96 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k3
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$check$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$check$0 0) (=> (= reftgen$check$0 a0) (> a0 0)) (>= a0 0) (not (not (= a0 reftgen$check$0)))) (k0 a0 reftgen$check$0 a0))))
(assert (forall ((reftgen$check$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (>= reftgen$check$0 0) (=> (= reftgen$check$0 a0) (> a0 0)) (>= a0 0) (not (not (= a0 reftgen$check$0))) (k0 a1 reftgen$check$0 a0) (not (> a1 0))) false)))

(check-sat)
