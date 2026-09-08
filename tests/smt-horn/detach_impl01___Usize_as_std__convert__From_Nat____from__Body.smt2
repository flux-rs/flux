(set-logic HORN)

;; Tag 0: Ret at 36:5: 36:6 (ESpan { span: tests/pos/detached/detach_impl01.rs:79:32: 79:33 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (= reftgen$n$0 (mkadt0$0 0))) (k0 0 (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a0 Adt0)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (= reftgen$n$0 (mkadt0$0 (+ (fld0$0 a0) 1))) (<= 0 (fld0$0 a0)) (>= (fld0$0 a0) 0)) (k0 (+ 1 (fld0$0 a0)) (fld0$0 reftgen$n$0)))))
(assert (forall ((reftgen$n$0 Adt0)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$0)) (k0 a1 (fld0$0 reftgen$n$0)) (not (= a1 (fld0$0 reftgen$n$0)))) false)))

(check-sat)
