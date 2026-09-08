(set-logic HORN)

;; Tag 0: Call at 26:9: 26:16 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:64:16: 64:21 (#0), base: None })
;; Tag 1: Call at 27:9: 27:16 (ESpan { span: tests/pos/surface/../../lib/rvec.rs:64:16: 64:21 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k3
(declare-fun k0 (Int Int) Bool)

(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$1)) (>= (fld0$0 reftgen$n$1) 0) (not (not (= (fld0$0 reftgen$n$1) 10))) (not (> (fld0$0 reftgen$n$1) 0))) false)))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a0 Int)) (=> (and (<= 0 (fld0$0 reftgen$n$1)) (>= (fld0$0 reftgen$n$1) 0) (not (not (= (fld0$0 reftgen$n$1) 10)))) (k0 a0 (fld0$0 reftgen$n$1)))))
(assert (forall ((reftgen$n$1 Adt0)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)) (=> (and (<= 0 (fld0$0 reftgen$n$1)) (>= (fld0$0 reftgen$n$1) 0) (not (not (= (fld0$0 reftgen$n$1) 10))) (<= 0 (- (fld0$0 reftgen$n$1) 1)) (k0 a1 (fld0$0 reftgen$n$1)) (not (> (fld0$0 reftgen$n$1) 0))) false)))

(check-sat)
