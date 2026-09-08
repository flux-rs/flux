(set-logic HORN)

;; Tag 0: Call at 25:5: 25:24 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)) (=> (= 42 (fld0$0 a0)) (k0 (fld0$0 a0)))))
(assert (forall ((a1 Adt0)(_$ Int)) (=> (and (k0 (fld0$0 a1)) (not (= (= (fld0$0 a1) 42) true))) false)))

(check-sat)
