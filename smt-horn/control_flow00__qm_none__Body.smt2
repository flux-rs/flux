(set-logic HORN)

;; Tag 0: Ret at 65:5: 65:12 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:62:46: 62:51 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)) (=> true (k0 a0))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)) (=> (and (= (mkadt0$0 false) (mkadt0$0 true)) (k0 a1) (not false)) false)))

(check-sat)
