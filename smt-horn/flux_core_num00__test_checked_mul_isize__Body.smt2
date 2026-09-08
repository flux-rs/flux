(set-logic HORN)

;; Tag 0: Call at 113:12: 113:42 (ESpan { span: lib/flux-core/src/option.rs:46:24: 46:28 (#0), base: None })
;; Tag 1: Call at 113:5: 113:49 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Call at 114:5: 114:48 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 3: Call at 115:5: 115:48 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(define-fun c0 () Int (- 9223372036854775808))
(define-fun c1 () Int 9223372036854775807)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((_$ Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (= c1 9223372036854775807) (= c0 (- 9223372036854775808)) (= a0 (* 3 4))) (k0 a0))))
(assert (forall ((_$ Int)(_$ Int)) (=> (and (= c1 9223372036854775807) (= c0 (- 9223372036854775808)) (not (= (and (>= (* 3 4) c0) (<= (* 3 4) c1)) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 9223372036854775807) (= c0 (- 9223372036854775808)) (k0 a1) (not (= (= a1 12) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 9223372036854775807) (= c0 (- 9223372036854775808)) (k0 a1) (not (= (not (and (>= (* 9223372036854775807 2) c0) (<= (* 9223372036854775807 2) c1))) true))) false)))
(assert (forall ((_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (= c1 9223372036854775807) (= c0 (- 9223372036854775808)) (k0 a1) (not (= (not (and (>= (* (- 9223372036854775808) 2) c0) (<= (* (- 9223372036854775808) 2) c1))) true))) false)))

(check-sat)
