(set-logic HORN)

;; Tag 0: Ret at 80:5: 80:6 (ESpan { span: tests/with_deps/pos/surface/primops00.rs:76:32: 76:38 (#0), base: None })

(declare-type-var T0)
(declare-const c0 (Array Int (Array Int Int)))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Bool) Bool)

(assert (forall ((a0 Bool)(_$ Int)) (=> (not a0) (k0 6 a0))))
(assert (forall ((a0 Bool)(_$ Int)(_$ Int)) (=> (and a0 (<= (c0 10 7) 7)) (k0 (c0 10 7) true))))
(assert (forall ((a0 Bool)(a1 Int)(_$ Int)) (=> (and (k0 a1 a0) (not (<= a1 7))) false)))

(check-sat)
