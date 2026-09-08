(set-logic HORN)

;; Tag 0: Call at 208:12: 208:42 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 208:5: 208:49 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 209:5: 209:48 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(define-fun c0 () Int 18446744073709551615)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((_$ Int)(a0 Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (= a0 (* 3 4))) (k0 a0))))
(assert (forall ((_$ Int)) (=> (and (= c0 18446744073709551615) (not (= (<= (* 3 4) c0) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (not (= (= a1 12) true))) false)))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (= c0 18446744073709551615) (k0 a1) (>= a1 0) (not (= (not (<= (* 18446744073709551615 2) c0)) true))) false)))

(check-sat)
