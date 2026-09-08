(set-logic HORN)

;; Tag 0: Call at 40:5: 40:24 (ESpan { span: tests/pos/surface/closure02.rs:28:26: 28:33 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (< 0 (fld0$0 a0)) (<= 0 (fld0$0 a0)) (<= 10 a1)) (k0 a1 (fld0$0 a0)))))
(assert (forall ((a0 Adt0)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (< 0 (fld0$0 a0)) (<= 0 (fld0$0 a0)) (k0 a2 (fld0$0 a0)) (not (<= 10 a2))) false)))

(check-sat)
