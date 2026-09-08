(set-logic HORN)

;; Tag 0: Assign at 26:13: 26:31 (ESpan { span: tests/pos/surface/range.rs:7:25: 7:32 (#0), base: None })
;; Tag 1: Assign at 26:13: 26:31 (ESpan { span: tests/pos/surface/range.rs:7:36: 7:43 (#0), base: None })
;; Tag 2: Ret at 27:13: 27:22 (ESpan { span: tests/pos/surface/range.rs:21:62: 21:69 (#0), base: None })
;; Tag 3: Ret at 27:13: 27:22 (ESpan { span: tests/pos/surface/range.rs:21:73: 21:79 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int Int) Bool)

(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (not (<= reftgen$lo$0 (+ a0 1)))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (not (<= (+ a0 1) reftgen$hi$1))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1)) (k0 a0 reftgen$lo$0 reftgen$hi$1 a0))))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (k0 a1 reftgen$lo$0 reftgen$hi$1 a0) (not (<= reftgen$lo$0 a1))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (k0 a1 reftgen$lo$0 reftgen$hi$1 a0) (not (< a1 reftgen$hi$1))) false)))

(check-sat)
