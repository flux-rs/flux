(set-logic HORN)

;; Tag 0: Ret at 138:37: 138:41 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:136:44: 136:49 (#0), base: None })
;; Tag 1: Underflow at 138:21: 138:26
;; Tag 2: Ret at 138:16: 138:27

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (not (> reftgen$n$0 0)) (not (= false (> reftgen$n$0 0)))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$n$0 0) (not (>= (- reftgen$n$0 1) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$n$0 0)) (k0 (- reftgen$n$0 1) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (> reftgen$n$0 0) (k0 a0 reftgen$n$0) (not (= a0 (- reftgen$n$0 1)))) false)))

(check-sat)
