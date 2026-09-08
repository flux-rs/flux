(set-logic HORN)

;; Tag 0: Ret at 19:5: 19:8 (ESpan { span: tests/pos/surface/scrape01.rs:10:60: 10:65 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$lo$0 0) (<= reftgen$lo$0 reftgen$hi$1) (>= reftgen$hi$1 0)) (k0 reftgen$lo$0 0 reftgen$lo$0 reftgen$hi$1))))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$lo$0 0) (<= reftgen$lo$0 reftgen$hi$1) (>= reftgen$hi$1 0)) (k1 0 reftgen$lo$0 reftgen$hi$1))))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$lo$0 0) (<= reftgen$lo$0 reftgen$hi$1) (>= reftgen$hi$1 0) (k0 a0 a1 reftgen$lo$0 reftgen$hi$1) (k1 a1 reftgen$lo$0 reftgen$hi$1) (not (< a0 reftgen$hi$1)) (not (= a1 (- reftgen$hi$1 reftgen$lo$0)))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$lo$0 0) (<= reftgen$lo$0 reftgen$hi$1) (>= reftgen$hi$1 0) (k0 a0 a1 reftgen$lo$0 reftgen$hi$1) (k1 a1 reftgen$lo$0 reftgen$hi$1) (< a0 reftgen$hi$1) (<= 0 (+ a1 1))) (k0 (+ a0 1) (+ a1 1) reftgen$lo$0 reftgen$hi$1))))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$lo$0 0) (<= reftgen$lo$0 reftgen$hi$1) (>= reftgen$hi$1 0) (k0 a0 a1 reftgen$lo$0 reftgen$hi$1) (k1 a1 reftgen$lo$0 reftgen$hi$1) (< a0 reftgen$hi$1) (<= 0 (+ a1 1))) (k1 (+ a1 1) reftgen$lo$0 reftgen$hi$1))))

(check-sat)
