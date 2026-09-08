(set-logic HORN)

;; Tag 0: Ret at 101:20: 101:21 (ESpan { span: tests/pos/surface/simplex.rs:95:105: 95:110 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int) Bool)

(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(reftgen$j$2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (< 0 reftgen$m$0) (>= reftgen$m$0 0) (< 0 reftgen$n$1) (>= reftgen$n$1 0) (< 0 reftgen$j$2) (< reftgen$j$2 reftgen$n$1) (>= reftgen$j$2 0)) (k0 1 reftgen$m$0 reftgen$n$1 reftgen$j$2))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(reftgen$j$2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (< 0 reftgen$m$0) (>= reftgen$m$0 0) (< 0 reftgen$n$1) (>= reftgen$n$1 0) (< 0 reftgen$j$2) (< reftgen$j$2 reftgen$n$1) (>= reftgen$j$2 0) (k0 a0 reftgen$m$0 reftgen$n$1 reftgen$j$2) (< a0 reftgen$m$0) (not a1)) (k0 (+ a0 1) reftgen$m$0 reftgen$n$1 reftgen$j$2))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(reftgen$j$2 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Bool)(_$ Int)) (=> (and (< 0 reftgen$m$0) (>= reftgen$m$0 0) (< 0 reftgen$n$1) (>= reftgen$n$1 0) (< 0 reftgen$j$2) (< reftgen$j$2 reftgen$n$1) (>= reftgen$j$2 0) (k0 a0 reftgen$m$0 reftgen$n$1 reftgen$j$2) (< a0 reftgen$m$0) a1 (not (< 0 a0))) false)))

(check-sat)
