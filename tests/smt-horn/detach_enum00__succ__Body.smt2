(set-logic HORN)

;; Tag 0: Ret at 12:1: 12:2 (ESpan { span: tests/pos/detached/detach_enum00.rs:29:27: 29:30 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)) (=> (<= 0 (fld0$0 reftgen$n$0)) (k0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Adt0)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (k0 (fld0$0 a0) (fld0$0 reftgen$n$0)) (<= 0 (fld0$0 a0)) (not (= (+ (fld0$0 a0) 1) (+ (fld0$0 reftgen$n$0) 1)))) false)))

(check-sat)
