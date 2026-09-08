(set-logic HORN)

;; Tag 0: Ret at 16:5: 16:12 (ESpan { span: tests/pos/surface/issue-271.rs:11:38: 11:45 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((reftgen$x$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$x$0 0) (not (>= reftgen$x$0 100))) (k0 reftgen$x$0))))
(assert (forall ((reftgen$x$0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$x$0 0) (not (>= reftgen$x$0 100)) (k0 reftgen$x$0) (not (< reftgen$x$0 100))) false)))

(check-sat)
