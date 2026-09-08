(set-logic HORN)

;; Tag 0: Call at 119:12: 119:43 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 119:5: 119:49 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 120:12: 120:46 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 3: Call at 120:5: 120:53 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 4: Call at 121:12: 121:47 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 5: Call at 121:5: 121:53 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 6: Call at 122:12: 122:44 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 7: Call at 122:5: 122:51 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 8: Call at 124:5: 124:49 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
;; rust const: core::num::<impl isize>::MIN
(define-fun c0 () Int (- 9223372036854775808))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int) Bool)
;; orig: $k2
(declare-fun k2 (Int Int Int) Bool)
;; orig: $k3
(declare-fun k3 (Int Int Int Int) Bool)

(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (= a0 (div 10 2))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (not (= (or (not (= 10 c0)) (not (= 2 (- 1)))) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (not (= (= a1 5) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (= a2 (- (div (- (- 10)) 3)))) (k1 a2 a1))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (not (= (or (not (= (- 10) c0)) (not (= 3 (- 1)))) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (not (= (= a3 (- 3)) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (= a4 (div (- (- 10)) (- (- 3))))) (k2 a4 a1 a3))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (not (= (or (not (= (- 10) c0)) (not (= (- 3) (- 1)))) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (k2 a5 a1 a3) (not (= (= a5 3) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)(a6 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (k2 a5 a1 a3) (= a6 (- (div 10 (- (- 3)))))) (k3 a6 a1 a3 a5))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (k2 a5 a1 a3) (not (= (or (not (= 10 c0)) (not (= (- 3) (- 1)))) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (k2 a5 a1 a3) (k3 a7 a1 a3 a5) (not (= (= a7 (- 3)) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a5 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (= c0 (- 9223372036854775808)) (k0 a1) (k1 a3 a1) (k2 a5 a1 a3) (k3 a7 a1 a3 a5) (not (= (not (or (not (= (- 9223372036854775808) c0)) (not (= (- 1) (- 1))))) true))) false)))

(check-sat)
