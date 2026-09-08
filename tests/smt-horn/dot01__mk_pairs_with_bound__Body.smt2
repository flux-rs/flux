(set-logic HORN)

;; Tag 0: Ret at 26:5: 26:8 (ESpan { span: tests/pos/structs/dot01.rs:17:41: 17:55 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int) Bool)
;; orig: $k1
(declare-fun k2 (Int Int Int Int Int) Bool)
;; orig: $k1
(declare-fun k3 (Int Int Int Int) Bool)
;; orig: $k3
(declare-fun k4 (Int Int Int Int Int) Bool)
;; orig: $k3
(declare-fun k5 (Int Int Int Int) Bool)

(assert (forall ((reftgen$a$0 Int)(_$ Int)) (=> true (k0 0 0 reftgen$a$0))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)) (=> true (k1 0 reftgen$a$0))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (not (< a0 reftgen$a$0)) (k2 (fld0$0 a2) (fld0$1 a2) a0 a1 reftgen$a$0) (k3 (fld0$1 a2) a0 a1 reftgen$a$0) (not (<= (+ (fld0$0 a2) (fld0$1 a2)) reftgen$a$0))) false)))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (k2 (fld0$0 a3) (fld0$1 a3) a0 a1 reftgen$a$0) (k3 (fld0$1 a3) a0 a1 reftgen$a$0)) (k4 (fld0$0 a3) (fld0$1 a3) reftgen$a$0 a0 a1))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (k2 (fld0$0 a3) (fld0$1 a3) a0 a1 reftgen$a$0) (k3 (fld0$1 a3) a0 a1 reftgen$a$0)) (k5 (fld0$1 a3) reftgen$a$0 a0 a1))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0)) (k4 a0 (- reftgen$a$0 a0) reftgen$a$0 a0 a1))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0)) (k5 (- reftgen$a$0 a0) reftgen$a$0 a0 a1))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (<= 0 (+ a1 1))) (k0 (+ a0 1) (+ a1 1) reftgen$a$0))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (<= 0 (+ a1 1))) (k1 (+ a1 1) reftgen$a$0))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Adt0)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (<= 0 (+ a1 1)) (k4 (fld0$0 a4) (fld0$1 a4) reftgen$a$0 a0 a1) (k5 (fld0$1 a4) reftgen$a$0 a0 a1)) (k2 (fld0$0 a4) (fld0$1 a4) (+ a0 1) (+ a1 1) reftgen$a$0))))
(assert (forall ((reftgen$a$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a4 Adt0)(_$ Int)) (=> (and (k0 a0 a1 reftgen$a$0) (k1 a1 reftgen$a$0) (< a0 reftgen$a$0) (<= 0 (+ a1 1)) (k4 (fld0$0 a4) (fld0$1 a4) reftgen$a$0 a0 a1) (k5 (fld0$1 a4) reftgen$a$0 a0 a1)) (k3 (fld0$1 a4) (+ a0 1) (+ a1 1) reftgen$a$0))))

(check-sat)
