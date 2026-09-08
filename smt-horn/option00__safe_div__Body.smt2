(set-logic HORN)

;; Tag 0: Assert("possible division by zero") at 47:46: 47:69
;; Tag 1: Ret at 47:41: 47:70
;; Tag 2: Ret at 47:27: 47:31 (ESpan { span: tests/with_deps/pos/enums/option00.rs:45:86: 45:102 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$numerator$0 Int)(reftgen$denominator$1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$numerator$0 0) (>= reftgen$denominator$1 0) (not (= reftgen$denominator$1 0)) (not (not (= reftgen$denominator$1 0)))) false)))
(assert (forall ((reftgen$numerator$0 Int)(reftgen$denominator$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$numerator$0 0) (>= reftgen$denominator$1 0) (not (= reftgen$denominator$1 0)) (not (= reftgen$denominator$1 0))) (k0 (div reftgen$numerator$0 reftgen$denominator$1) reftgen$numerator$0 reftgen$denominator$1))))
(assert (forall ((reftgen$numerator$0 Int)(reftgen$denominator$1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (>= reftgen$numerator$0 0) (>= reftgen$denominator$1 0) (not (= reftgen$denominator$1 0)) (not (= reftgen$denominator$1 0)) (k0 a0 reftgen$numerator$0 reftgen$denominator$1) (not (= a0 (div reftgen$numerator$0 reftgen$denominator$1)))) false)))
(assert (forall ((reftgen$numerator$0 Int)(reftgen$denominator$1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$numerator$0 0) (>= reftgen$denominator$1 0) (not (not (= reftgen$denominator$1 0))) (not (= false (not (= reftgen$denominator$1 0))))) false)))

(check-sat)
