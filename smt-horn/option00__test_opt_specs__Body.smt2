(set-logic HORN)

;; Tag 0: Call at 42:5: 42:20 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 42)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (= (= a1 42) true))) false)))

(check-sat)
