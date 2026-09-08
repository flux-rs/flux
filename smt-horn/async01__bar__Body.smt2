(set-logic HORN)

;; Tag 0: Call at 12:5: 12:19 (ESpan { span: tests/pos/surface/async01.rs:1:21: 1:25 (#0), base: None })
;; Tag 1: Call at 13:5: 13:19 (ESpan { span: tests/pos/surface/async01.rs:1:21: 1:25 (#0), base: None })
;; Tag 2: Ret at 14:5: 14:10 (ESpan { span: tests/pos/surface/async01.rs:9:39: 9:43 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$y$0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$y$0) (not (> reftgen$y$0 10))) (k0 0 reftgen$y$0))))
(assert (forall ((reftgen$y$0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 reftgen$y$0) (> reftgen$y$0 10)) (k0 1 reftgen$y$0))))
(assert (forall ((reftgen$y$0 Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (<= 0 reftgen$y$0) (k0 a0 reftgen$y$0) (not (= (>= a0 0) true))) false)))
(assert (forall ((reftgen$y$0 Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (<= 0 reftgen$y$0) (k0 a0 reftgen$y$0) (not (= (>= reftgen$y$0 0) true))) false)))
(assert (forall ((reftgen$y$0 Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (<= 0 reftgen$y$0) (k0 a0 reftgen$y$0) (not (<= reftgen$y$0 (+ reftgen$y$0 a0)))) false)))

(check-sat)
