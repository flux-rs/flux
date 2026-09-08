(set-logic HORN)

;; Tag 0: Call at 49:12: 49:40 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 49:5: 49:47 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 50:5: 50:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 3: Call at 51:5: 51:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
;; rust const: core::num::<impl i32>::MIN
(define-fun c0 () Int (- 2147483648))
;; rust const: core::num::<impl i32>::MAX
(define-fun c1 () Int 2147483647)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)

(assert (forall ((_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (= c1 2147483647) (= c0 (- 2147483648)) (= a0 (* 3 4))) (k0 a0))))
(assert (forall ((_$ Int)(_$ Int)) (=> (and (= c1 2147483647) (= c0 (- 2147483648)) (not (= (and (>= (* 3 4) c0) (<= (* 3 4) c1)) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 2147483647) (= c0 (- 2147483648)) (k0 a1) (not (= (= a1 12) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 2147483647) (= c0 (- 2147483648)) (k0 a1) (not (= (not (and (>= (* 2147483647 2) c0) (<= (* 2147483647 2) c1))) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 2147483647) (= c0 (- 2147483648)) (k0 a1) (not (= (not (and (>= (* (- 2147483648) 2) c0) (<= (* (- 2147483648) 2) c1))) true))) false)))

(check-sat)
