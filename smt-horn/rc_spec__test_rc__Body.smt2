(set-logic HORN)

;; Tag 0: Call at 11:5: 11:28 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 String)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (String) Bool)
(declare-fun k1 (String) Bool)

(assert (=> true (k0 ""bob"")))
(assert (forall ((a0 Adt0)(_$ Int)) (=> (k0 (fld0$0 a0)) (k1 (fld0$0 a0)))))
(assert (forall ((_$ Int)) (=> (and (k1 ""bob"") (not (= (= (mkadt0$0 ""bob"") (mkadt0$0 ""bob"")) true))) false)))

(check-sat)
