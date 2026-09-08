(set-logic HORN)

;; Tag 0: Call at 101:5: 101:33 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 1)) ((par (Par0) ((mkadt0$0 (fld0$0 Par0) (fld0$1 Par0))))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (=> true (k0 0)))
(assert (=> true (k0 0)))
(assert (forall ((_$ Int)(_$ Int)(a0 (Adt0 Int))(_$ Int)) (=> (and (k0 0) (=> false (= (fld0$0 a0) (+ 0 1))) (=> true (= (fld0$0 a0) 0)) (= (fld0$1 a0) 0) (not (= (= (fld0$0 a0) 0) true))) false)))

(check-sat)
