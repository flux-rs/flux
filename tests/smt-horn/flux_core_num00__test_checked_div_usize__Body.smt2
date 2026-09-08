(set-logic HORN)

;; Tag 0: Call at 213:5: 213:49 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (= a0 (div 10 2)) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1) (>= a1 0) (not (= (= a1 5) true))) false)))

(check-sat)
