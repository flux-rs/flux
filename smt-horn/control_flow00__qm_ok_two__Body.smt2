(set-logic HORN)

;; Tag 0: Ret at 1:1: 1:1 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:92:79: 92:83 (#0), base: None })
;; Tag 1: Ret at 1:1: 1:1 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:92:79: 92:83 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)) (((mkadt0$0 (fld0$0 Bool)))((mkadt1$0 (fld1$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Int)) (=> true (k0 a0))))
(assert (forall ((_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt1)) (=> (and (= (mkadt0$0 true) (mkadt0$0 true)) (k0 a1) (= (mkadt0$0 true) (mkadt0$0 false)) (not false)) false)))
(assert (forall ((_$ Int)(a3 Adt1)) (=> (and (= (mkadt0$0 true) (mkadt0$0 false)) (not false)) false)))

(check-sat)
