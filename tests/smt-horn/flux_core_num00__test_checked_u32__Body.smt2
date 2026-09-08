(set-logic HORN)

;; Tag 0: Underflow at 147:12: 147:26
;; Tag 1: Call at 147:12: 147:50 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 2: Call at 147:5: 147:63 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 3: Call at 148:5: 148:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 4: Call at 149:5: 149:46 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
;; rust const: core::num::<impl u32>::MAX
(define-fun c0 () Int 4294967295)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k2
(declare-fun k1 (Int Int) Bool)

(assert (forall ((_$ Int)) (=> (and (= c0 4294967295) (not (>= (- 4294967295 1) 0))) false)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 4294967295) (= a0 (+ (- 4294967295 1) 1))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 4294967295) (not (= (<= (+ (- 4294967295 1) 1) c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (= a1 4294967295) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (not (= (not (<= (+ 4294967295 1) c0)) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (= a2 (- 5 3))) (k1 a2 a1))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (= c0 4294967295) (k0 a1) (>= a1 0) (k1 a3 a1) (>= a3 0) (not (= (= a3 2) true))) false)))

(check-sat)
