(set-logic HORN)

;; Tag 0: Ret at 31:1: 31:2 (ESpan { span: tests/pos/detached/detach_enum01.rs:19:50: 19:53 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k1
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(a0 Int)(_$ Int)) (=> (>= (fld0$0 reftgen$n$0) 0) (k0 (fld0$0 reftgen$n$0) (fld0$0 reftgen$n$0) a0))))
(assert (forall ((reftgen$n$0 Adt0)(a0 Int)(_$ Int)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (>= (fld0$0 reftgen$n$0) 0) (k0 (fld0$0 a1) (fld0$0 reftgen$n$0) a0) (>= (fld0$0 a1) 0) (not (= (+ (fld0$0 a1) 1) (+ (fld0$0 reftgen$n$0) 1)))) false)))

(check-sat)
