(set-logic HORN)

;; Tag 0: Fold at 57:5: 57:6 (ESpan { span: tests/pos/surface/too_many_linked_lists.rs:5:19: 5:27 (#0), base: None })
;; Tag 1: Ret at 57:5: 57:6 (ESpan { span: tests/pos/surface/too_many_linked_lists.rs:53:76: 53:79 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)) (((mkadt0$0 (fld0$0 Int)))((mkadt1$0 (fld1$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k4
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (>= (fld0$0 reftgen$n$1) 0) (k0 (fld0$0 reftgen$n$1) (fld0$0 reftgen$n$1) a0))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)(a1 Adt1)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (k0 (fld1$0 a1) (fld0$0 reftgen$n$1) a0) (>= (fld1$0 a1) 0) (not (>= (+ (fld1$0 a1) 1) 0))) false)))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)(a1 Adt1)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$1) 0) (k0 (fld1$0 a1) (fld0$0 reftgen$n$1) a0) (>= (fld1$0 a1) 0) (not (= (+ (fld1$0 a1) 1) (+ (fld0$0 reftgen$n$1) 1)))) false)))

(check-sat)
