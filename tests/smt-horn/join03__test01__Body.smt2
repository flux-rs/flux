(set-logic HORN)

;; Tag 0: Ret at 26:5: 26:11

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int) (fld0$1 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int Int Int Int) Bool)
;; orig: $k0
(declare-fun k2 (Int Int Int) Bool)

(assert (forall ((reftgen$p$0 Adt0)) (=> true (k0 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0) 0 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))
(assert (forall ((reftgen$p$0 Adt0)) (=> true (k1 (fld0$1 reftgen$p$0) 0 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))
(assert (forall ((reftgen$p$0 Adt0)) (=> true (k2 0 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Adt0)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 (fld0$0 a0) (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k1 (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k2 a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (not (< a1 10)) (not (= (fld0$0 a0) (fld0$0 reftgen$p$0)))) false)))
(assert (forall ((reftgen$p$0 Adt0)(a0 Adt0)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 (fld0$0 a0) (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k1 (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k2 a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (< a1 10)) (k0 (fld0$0 a0) (+ (fld0$1 a0) 1) (+ a1 1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Adt0)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 (fld0$0 a0) (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k1 (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k2 a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (< a1 10)) (k1 (+ (fld0$1 a0) 1) (+ a1 1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))
(assert (forall ((reftgen$p$0 Adt0)(a0 Adt0)(a1 Int)(_$ Int)(_$ Int)) (=> (and (k0 (fld0$0 a0) (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k1 (fld0$1 a0) a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (k2 a1 (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)) (< a1 10)) (k2 (+ a1 1) (fld0$0 reftgen$p$0) (fld0$1 reftgen$p$0)))))

(check-sat)
