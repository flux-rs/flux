(set-logic HORN)

;; Tag 0: Call at 69:5: 69:43 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 1: Call at 70:12: 70:43 (ESpan { span: lib/flux-core/src/result.rs:91:28: 91:32 (#0), base: None })
;; Tag 2: Call at 70:5: 70:55 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 3: Call at 71:5: 71:58 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
;; rust const: core::num::<impl u32>::MAX
(define-fun c0 () Int 4294967295)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k2
(declare-fun k0 (Int) Bool)

(assert (forall ((_$ Int)) (=> (and (= c0 4294967295) (not (= (<= 1000 c0) true))) false)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 4294967295) (= a0 1000)) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 4294967295) (not (= (<= 1000 c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (= a1 1000) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (not (<= (+ 4294967295 1) c0)) true))) false)))

(check-sat)
