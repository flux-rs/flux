(set-logic HORN)

;; Tag 0: Ret at 33:35: 33:42 (ESpan { span: tests/pos/surface/date.rs:31:33: 31:46 (#0), base: None })
;; Tag 1: Ret at 33:5: 33:42 (ESpan { span: tests/pos/surface/date.rs:31:33: 31:46 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((reftgen$m$0 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$m$0 0) (not (= reftgen$m$0 4)) (not (= reftgen$m$0 6)) (not (= reftgen$m$0 9)) (not (= (= reftgen$m$0 11) (or (or (or (= reftgen$m$0 4) (= reftgen$m$0 6)) (= reftgen$m$0 9)) (= reftgen$m$0 11))))) false)))
(assert (forall ((reftgen$m$0 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$m$0 0) (not (= reftgen$m$0 4)) (not (= reftgen$m$0 6)) (not (not (= reftgen$m$0 9)))) (k0 reftgen$m$0))))
(assert (forall ((reftgen$m$0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$m$0 0) (not (= reftgen$m$0 4)) (not (not (= reftgen$m$0 6)))) (k0 reftgen$m$0))))
(assert (forall ((reftgen$m$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$m$0 0) (not (not (= reftgen$m$0 4)))) (k0 reftgen$m$0))))
(assert (forall ((reftgen$m$0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$m$0 0) (k0 reftgen$m$0) (not (= true (or (or (or (= reftgen$m$0 4) (= reftgen$m$0 6)) (= reftgen$m$0 9)) (= reftgen$m$0 11))))) false)))

(check-sat)
