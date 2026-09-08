(set-logic HORN)

;; Tag 0: Call at 26:21: 26:27 (ESpan { span: tests/with_deps/pos/surface/closure12.rs:22:23: 22:29 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (<= 0 a0))) false)))
(assert (forall ((a1 Int)(_$ Int)) (=> (and (<= 0 a1) (< a1 10)) (k0 a1))))

(check-sat)
