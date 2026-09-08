(set-logic HORN)

;; Tag 0: Assign at 41:13: 41:31 (ESpan { span: tests/pos/surface/../../lib/rrange.rs:7:25: 7:32 (#0), base: None })
;; Tag 1: Assign at 41:13: 41:31 (ESpan { span: tests/pos/surface/../../lib/rrange.rs:7:36: 7:43 (#0), base: None })
;; Tag 2: Ret at 42:13: 42:22 (ESpan { span: tests/pos/surface/../../lib/rrange.rs:36:67: 36:74 (#0), base: None })
;; Tag 3: Ret at 42:13: 42:22 (ESpan { span: tests/pos/surface/../../lib/rrange.rs:36:78: 36:84 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int) Bool)

(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (not (<= reftgen$lo$0 (+ a0 1)))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (not (<= (+ a0 1) reftgen$hi$1))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1)) (k0 a0 reftgen$lo$0 reftgen$hi$1 a0))))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (k0 a1 reftgen$lo$0 reftgen$hi$1 a0) (not (<= reftgen$lo$0 a1))) false)))
(assert (forall ((reftgen$lo$0 Int)(reftgen$hi$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= reftgen$lo$0 a0) (<= a0 reftgen$hi$1) (< a0 reftgen$hi$1) (k0 a1 reftgen$lo$0 reftgen$hi$1 a0) (not (< a1 reftgen$hi$1))) false)))

(check-sat)
