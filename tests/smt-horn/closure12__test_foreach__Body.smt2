(set-logic HORN)

;; Tag 0: Call at 31:9: 31:23 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:10:17: 10:21 (#0), base: None })
;; Tag 1: Call at 32:9: 32:23 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:10:17: 10:21 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= (<= 0 a0) true))) false)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= (< a0 10) true))) false)))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (<= 0 a1) (< a1 10)) (k0 a1))))

(check-sat)
