(set-logic HORN)

;; Tag 0: Call at 46:33: 46:36 (ESpan { span: lib/flux-core/src/slice/index.rs:48:58: 48:67 (#0), base: None })
;; Tag 1: Call at 46:43: 46:46 (ESpan { span: lib/flux-core/src/slice/index.rs:48:58: 48:67 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0)) (k1 a1 (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (k0 a0 (fld0$0 reftgen$n$0)) (>= a0 0) (k1 a2 (fld0$0 reftgen$n$0) a0) (not (< a0 (fld0$0 reftgen$n$0)))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (< a3 (fld0$0 reftgen$n$0))) (k0 a3 (fld0$0 reftgen$n$0)))))

(check-sat)
