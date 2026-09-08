(set-logic HORN)

;; Tag 0: Ret at 14:5: 14:6 (ESpan { span: tests/with_deps/pos/surface/issue-1505.rs:8:45: 8:51 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; flux def: FluxId { parent: DefId(0:0 ~ issue_1505[1ee3]), name: "foo" }
(declare-fun f$foo$0 (Int) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 reftgen$n$0) (not (< a0 5)) (not (>= a0 5))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 reftgen$n$0) (< a0 5)) (k0 (+ a0 1) reftgen$n$0))))

(check-sat)
