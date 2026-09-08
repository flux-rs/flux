(set-logic HORN)

;; Tag 0: Call at 163:12: 163:40 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 163:5: 163:47 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 164:5: 164:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(define-fun c0 () Int 4294967295)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 4294967295) (= a0 (* 3 4))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 4294967295) (not (= (<= (* 3 4) c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (= a1 12) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (not (<= (* 4294967295 2) c0)) true))) false)))

(check-sat)
