(set-logic HORN)

;; Tag 0: Ret at 8:5: 8:10 (ESpan { span: tests/pos/surface/issue-271.rs:3:38: 3:45 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((reftgen$x$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$x$0 0) (not (>= reftgen$x$0 100))) (k0 reftgen$x$0))))
(assert (forall ((reftgen$x$0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$x$0 0) (not (>= reftgen$x$0 100)) (k0 reftgen$x$0) (not (< reftgen$x$0 100))) false)))

(check-sat)
