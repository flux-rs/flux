(set-logic HORN)

;; Tag 0: Ret at 14:5: 14:6 (ESpan { span: tests/pos/surface/ghostcell00.rs:6:28: 6:33 (#0), base: None })

(declare-type-var T0)
(declare-sort OpaqueAdt0 0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 OpaqueAdt0)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int OpaqueAdt0) Bool)
;; orig: $k1
(declare-fun k1 (Int OpaqueAdt0) Bool)
;; orig: $k2
(declare-fun k2 (Int OpaqueAdt0 Int) Bool)
;; orig: $k3
(declare-fun k3 (Int OpaqueAdt0 Int Int) Bool)

(assert (forall ((a0 Adt0)) (=> true (k0 42 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a1 Int)(_$ Int)) (=> (k0 a1 (fld0$0 a0)) (k1 a1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a2 Int)(_$ Int)) (=> (k1 a2 (fld0$0 a0)) (k0 a2 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)) (=> (k1 a3 (fld0$0 a0)) (k1 (+ a3 1) (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k0 a4 (fld0$0 a0))) (k2 a4 (fld0$0 a0) a3))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k2 a5 (fld0$0 a0) a3)) (k0 a5 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a6 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k2 a6 (fld0$0 a0) a3)) (k2 (+ a6 1) (fld0$0 a0) a3))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a6 Int)(_$ Int)(a7 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k2 a6 (fld0$0 a0) a3) (k0 a7 (fld0$0 a0))) (k3 a7 (fld0$0 a0) a3 a6))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a6 Int)(_$ Int)(a8 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k2 a6 (fld0$0 a0) a3) (k3 a8 (fld0$0 a0) a3 a6)) (k0 a8 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(a3 Int)(_$ Int)(a6 Int)(_$ Int)(a9 Int)(_$ Int)) (=> (and (k1 a3 (fld0$0 a0)) (k2 a6 (fld0$0 a0) a3) (k3 a9 (fld0$0 a0) a3 a6) (not (> a9 0))) false)))

(check-sat)
