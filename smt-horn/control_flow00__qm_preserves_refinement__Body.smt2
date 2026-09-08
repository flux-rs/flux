(set-logic HORN)

;; Tag 0: Ret at 57:5: 57:12 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:54:57: 54:62 (#0), base: None })
;; Tag 1: Ret at 58:2: 58:2 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:54:65: 54:69 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)) (((mkadt0$0 (fld0$0 Bool)))((mkadt1$0 (fld1$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)) (=> (> a0 0) (k0 a0))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= (mkadt0$0 true) (mkadt0$0 true)) (k0 a1)) (k1 a1 a1))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= (mkadt0$0 true) (mkadt0$0 true)) (k0 a1) (k1 a2 a1) (not (> a2 0))) false)))
(assert (forall ((_$ Int)(a3 Adt1)) (=> (and (= (mkadt0$0 true) (mkadt0$0 false)) (not false)) false)))

(check-sat)
