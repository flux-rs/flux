(set-logic HORN)

;; Tag 0: Call at 29:10: 29:34 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:51:43: 51:48 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a2 Adt0)(_$ Int)) (=> (and (< a0 reftgen$m$0) (>= a0 0) (< a1 reftgen$n$1) (>= a1 0) (>= reftgen$n$1 0) (<= 0 reftgen$m$0) (= a2 (mkadt0$0 reftgen$n$1))) (k0 (fld0$0 a2) reftgen$m$0 reftgen$n$1 a0 a1))))
(assert (forall ((reftgen$m$0 Int)(reftgen$n$1 Int)(a0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a3 Adt0)(_$ Int)(_$ Int)) (=> (and (< a0 reftgen$m$0) (>= a0 0) (< a1 reftgen$n$1) (>= a1 0) (>= reftgen$n$1 0) (<= 0 reftgen$m$0) (k0 (fld0$0 a3) reftgen$m$0 reftgen$n$1 a0 a1) (<= 0 (fld0$0 a3)) (not (< a1 (fld0$0 a3)))) false)))

(check-sat)
