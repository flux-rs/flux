(set-logic HORN)

;; Tag 0: Underflow at 192:12: 192:28
;; Tag 1: Call at 192:12: 192:52 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 2: Call at 192:5: 192:67 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 3: Call at 193:5: 193:48 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 4: Call at 194:5: 194:48 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(define-fun c0 () Int 18446744073709551615)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((_$ Int)) (=> (and (= c0 18446744073709551615) (not (>= (- 18446744073709551615 1) 0))) false)))
(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (= a0 (+ (- 18446744073709551615 1) 1))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 18446744073709551615) (not (= (<= (+ (- 18446744073709551615 1) 1) c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (not (= (= a1 18446744073709551615) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (not (= (not (<= (+ 18446744073709551615 1) c0)) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (= a2 (- 5 3))) (k1 a2 a1))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (k1 a3 a1) (>= a3 0) (not (= (= a3 2) true))) false)))

(check-sat)
