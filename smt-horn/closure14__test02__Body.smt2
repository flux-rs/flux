(set-logic HORN)

;; Tag 0: Ret at 24:5: 24:25 (ESpan { span: tests/with_deps/pos/surface/closure14.rs:22:28: 22:32 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Bool) Bool)

(assert (forall ((a0 Int)) (=> true (k0 true))))
(assert (forall ((a1 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a1)) (not (= (fld0$0 a1) true))) false)))

(check-sat)
