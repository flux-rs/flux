(set-logic HORN)

;; Tag 0: Ret at 24:1: 24:2 (ESpan { span: tests/pos/surface/refined_type_var00.rs:21:50: 21:71 (#0), base: None })

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Bool Int Int) Bool)

(assert (forall ((reftgen$b$0 Bool)(reftgen$n$1 Int)(reftgen$m$2 Int)(_$ Int)) (=> (not reftgen$b$0) (k0 reftgen$m$2 reftgen$b$0 reftgen$n$1 reftgen$m$2))))
(assert (forall ((reftgen$b$0 Bool)(reftgen$n$1 Int)(reftgen$m$2 Int)(_$ Int)) (=> reftgen$b$0 (k0 reftgen$n$1 true reftgen$n$1 reftgen$m$2))))
(assert (forall ((reftgen$b$0 Bool)(reftgen$n$1 Int)(reftgen$m$2 Int)(a0 Int)(_$ Int)) (=> (and (k0 a0 reftgen$b$0 reftgen$n$1 reftgen$m$2) (not (= a0 (ite reftgen$b$0 reftgen$n$1 reftgen$m$2)))) false)))

(check-sat)
