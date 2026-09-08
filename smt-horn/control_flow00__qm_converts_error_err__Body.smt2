(set-logic HORN)

;; Tag 0: Ret at 133:5: 133:10 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:130:60: 130:65 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)) (=> true (k0 a0))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= (mkadt0$0 false) (mkadt0$0 true)) (k0 a1) (not false)) false)))

(check-sat)
