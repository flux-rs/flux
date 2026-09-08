(set-logic HORN)

;; Tag 0: Call at 52:5: 52:22 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (= a0 (div 42 2)) (k0 a0))))
(assert (forall ((a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a1) (>= a1 0) (not (= (= a1 21) true))) false)))

(check-sat)
