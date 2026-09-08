(set-logic HORN)

;; Tag 0: Call at 14:14: 14:17 (ESpan { span: tests/pos/structs/issue-158.rs:8:31: 8:37 (#0), base: None })
;; Tag 1: Call at 14:14: 14:17 (ESpan { span: tests/pos/structs/../../lib/rvec.rs:189:48: 189:53 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (<= 0 (fld0$0 a0)) (>= a1 0)) (k0 a1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (<= 0 (fld0$0 a0)) (k0 a2 (fld0$0 a0)) (not (>= a2 0))) false)))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (<= 0 (fld0$0 a0)) (not (< 0 (fld0$0 a0)))) false)))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)) (=> (and (> (fld0$0 a0) 0) (<= 0 (fld0$0 a0))) (k0 0 (fld0$0 a0)))))

(check-sat)
