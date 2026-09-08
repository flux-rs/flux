(set-logic HORN)

;; Tag 0: Call at 167:9: 167:36 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(_$ Int)(a1 Int)) (=> (>= a0 0) (k0 a1 a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= a0 0) (= (mkadt0$0 (not (= a0 0))) (mkadt0$0 true)) (k0 a2 a0) (>= (- a0 1) 0) (not (= (= (- a0 1) (- a0 1)) true))) false)))

(check-sat)
