(set-logic HORN)

;; Tag 0: Ret at 90:5: 90:14 (ESpan { span: tests/pos/surface/opt_blowup.rs:80:36: 80:41 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int) Bool)
;; orig: $k1
(declare-fun k1 (Int Int Int) Bool)
;; orig: $k2
(declare-fun k2 (Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)) (=> (< reftgen$n$0 a0) (k0 a0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (< a1 a2)) (k1 a2 reftgen$n$0 a1))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (k1 a3 reftgen$n$0 a1)) (k2 a3 reftgen$n$0 a1 a3))))
(assert (forall ((reftgen$n$0 Int)(a1 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (k0 a1 reftgen$n$0) (k1 a3 reftgen$n$0 a1) (k2 a4 reftgen$n$0 a1 a3) (not (< reftgen$n$0 a4))) false)))

(check-sat)
