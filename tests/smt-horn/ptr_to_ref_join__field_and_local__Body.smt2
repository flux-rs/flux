(set-logic HORN)

;; Tag 0: Call at 39:5: 39:12 (ESpan { span: tests/pos/fold_unfold/ptr_to_ref_join.rs:21:33: 21:40 (#0), base: None })
;; Tag 1: Call at 40:5: 40:24 (ESpan { span: tests/pos/fold_unfold/ptr_to_ref_join.rs:18:21: 18:25 (#0), base: None })
;; Tag 2: Call at 41:5: 41:20 (ESpan { span: tests/pos/fold_unfold/ptr_to_ref_join.rs:18:21: 18:25 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k4
(declare-fun k0 (Int Int Int Bool Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Bool Int) Bool)
;; orig: $k1
(declare-fun k2 (Int Int Int Bool Int) Bool)
;; orig: $k2
(declare-fun k3 (Int Int Int Bool Int) Bool)
;; orig: $k3
(declare-fun k4 (Int Int Int Bool Int) Bool)
;; orig: $k5
(declare-fun k5 (Int Int Int Bool Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k0 a1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k2 (fld0$1 reftgen$n$0) (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k0 a2 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1)) (k3 a2 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k0 a3 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1)) (k4 a3 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (not a0) (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k4 a4 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1)) (k0 a4 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k5 (fld0$1 reftgen$n$0) (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k5 a5 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1)) (k2 a5 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0)) (k3 a1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a6 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k5 a6 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1)) (k4 a6 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) a0 (>= (fld0$0 reftgen$n$0) 0) (>= (fld0$1 reftgen$n$0) 0) (k4 a7 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1)) (k5 a7 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) true a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a8 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (k4 a8 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (not (>= a8 10))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a9 Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (>= a9 10)) (k4 a9 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a10 Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (>= a10 0) (k2 a10 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (>= a11 0) (k3 a11 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (not (= (>= a10 10) true))) false)))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Bool)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a10 Int)(_$ Int)(_$ Int)(a11 Int)(_$ Int)(_$ Int)) (=> (and (>= (fld0$1 reftgen$n$0) 10) (>= a1 10) (>= a1 0) (k1 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (>= a10 0) (k2 a10 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (>= a11 0) (k3 a11 (fld0$0 reftgen$n$0) (fld0$1 reftgen$n$0) a0 a1) (not (= (>= a11 10) true))) false)))

(check-sat)
