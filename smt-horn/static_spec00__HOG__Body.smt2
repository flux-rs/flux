(set-logic HORN)

;; Tag 0: Ret at 18:24: 18:36 (ESpan { span: tests/pos/surface/static_spec00.rs:17:21: 17:28 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 67)))
(assert (=> true (k0 67)))
(assert (=> true (k0 67)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (< a0 100))) false)))

(check-sat)
