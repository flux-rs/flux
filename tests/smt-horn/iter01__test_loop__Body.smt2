(set-logic HORN)

;; Tag 0: Call at 18:9: 18:25 (ESpan { span: tests/pos/surface/iter01.rs:5:21: 5:25 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k2
(declare-fun k0 (Int Int) Bool)
;; orig: $k0
(declare-fun k1 (Int) Bool)
;; orig: $k1
(declare-fun k2 (Int Int) Bool)
;; orig: $k3
(declare-fun k3 (Int Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (<= 0 a1)) (k0 a1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)) (=> (<= 0 (fld0$0 a0)) (k1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(a2 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (k0 a2 (fld0$0 a0))) (k2 a2 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (k1 (fld0$0 a0)) (k2 a3 (fld0$0 a0))) (k3 a3 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (k1 (fld0$0 a0)) (k3 a4 (fld0$0 a0)) (not (= (<= 0 a4) true))) false)))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 a0)) (k1 (fld0$0 a0)) (k3 a4 (fld0$0 a0)) (k3 a5 (fld0$0 a0))) (k2 a5 (fld0$0 a0)))))

(check-sat)
