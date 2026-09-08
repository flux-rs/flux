(set-logic HORN)

;; Tag 0: Ret at 14:5: 14:6 (ESpan { span: tests/with_deps/pos/surface/issue-1505.rs:8:45: 8:51 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun f$foo$0 (Int) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 reftgen$n$0) (not (< a0 5)) (not (>= a0 5))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 reftgen$n$0) (< a0 5)) (k0 (+ a0 1) reftgen$n$0))))

(check-sat)
