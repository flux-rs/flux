(set-logic HORN)

;; Tag 0: Ret at 10:25: 10:37 (ESpan { span: tests/pos/surface/static_spec00.rs:9:19: 9:21 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 67)))
(assert (=> true (k0 67)))
(assert (=> true (k0 67)))
(assert (forall ((a0 Int)(_$ Int)) (=> (and (k0 a0) (not (= a0 67))) false)))

(check-sat)
