(set-logic HORN)

;; Tag 0: Call at 27:5: 27:20 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int) Bool)

(assert (=> true (k0 42)))
(assert (forall ((a0 Int)(_$ Int)) (=> (k0 a0) (k1 a0))))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (k1 a1) (not (= (= a1 42) true))) false)))

(check-sat)
