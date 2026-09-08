(set-logic HORN)

;; Tag 0: Call at 43:12: 43:39 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 43:5: 43:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 44:12: 44:39 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 3: Call at 44:5: 44:45 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 4: Call at 45:5: 45:45 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
;; rust const: core::num::<impl i32>::MIN
(define-fun c0 () Int (- 2147483648))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)

(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (= a0 (- 5))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 (- 2147483648)) (not (= (> 5 c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (k0 a1) (not (= (= a1 (- 5)) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (k0 a1) (= a2 (- 0))) (k1 a2 a1))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (k0 a1) (not (= (> 0 c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (k0 a1) (k1 a3 a1) (not (= (= a3 0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= c0 (- 2147483648)) (k0 a1) (k1 a3 a1) (not (= (not (> (- 2147483648) c0)) true))) false)))

(check-sat)
