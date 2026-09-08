(set-logic HORN)

;; Tag 0: Ret at 48:21: 48:32 (ESpan { span: tests/pos/surface/opt_blowup.rs:46:36: 46:41 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$k$0 Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (=> (>= reftgen$k$0 0) (= a0 (mod reftgen$k$0 2))) (not (not (= a0 0)))) (k0 (+ reftgen$k$0 1) reftgen$k$0 a0))))
(assert (forall ((reftgen$k$0 Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (=> (>= reftgen$k$0 0) (= a0 (mod reftgen$k$0 2))) (not (not (= a0 0))) (k0 a1 reftgen$k$0 a0) (not (< reftgen$k$0 a1))) false)))

(check-sat)
