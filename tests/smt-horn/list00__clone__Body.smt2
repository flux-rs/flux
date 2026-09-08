(set-logic HORN)

;; Tag 0: Underflow at 52:45: 52:50
;; Tag 1: Ret at 49:5: 53:6 (ESpan { span: tests/pos/enums/list00.rs:47:39: 47:40 (#0), base: None })
;; Tag 2: Ret at 50:9: 50:18 (ESpan { span: tests/pos/enums/list00.rs:47:39: 47:40 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0 (fld0$0 Int)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (not (= reftgen$n$0 0)) (not (>= (- reftgen$n$0 1) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (not (= reftgen$n$0 0)) (>= (- reftgen$n$0 1) 0)) (k0 (- reftgen$n$0 1) reftgen$n$0 a0))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(_$ Int)(_$ Int)(a1 Adt0)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (not (= reftgen$n$0 0)) (>= (- reftgen$n$0 1) 0) (k0 (fld0$0 a1) reftgen$n$0 a0) (>= (fld0$0 a1) 0) (not (= (+ (fld0$0 a1) 1) reftgen$n$0))) false)))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (not (not (= reftgen$n$0 0))) (not (= 0 reftgen$n$0))) false)))

(check-sat)
