(set-logic HORN)

;; Tag 0: Ret at 145:5: 145:12
;; Tag 1: Ret at 145:5: 145:12 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:141:44: 141:49 (#0), base: None })
;; Tag 2: Ret at 1:1: 1:1 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:141:44: 141:49 (#0), base: None })
;; Tag 3: Ret at 1:1: 1:1 (ESpan { span: tests/with_deps/pos/extern_specs/control_flow00.rs:141:44: 141:49 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)(Adt1 0)) (((mkadt0$0 (fld0$0 Bool)))((mkadt1$0 (fld1$0 Bool)))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int Int) Bool)
(declare-fun k2 (Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= a0 (- reftgen$n$0 1))) (k0 a0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 true)) (k0 a1 reftgen$n$0) (>= a1 0) (= a2 (- a1 1))) (k1 a2 reftgen$n$0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 true)) (k0 a1 reftgen$n$0) (>= a1 0) (= (mkadt0$0 (> a1 0)) (mkadt0$0 true)) (k1 a3 reftgen$n$0 a1) (>= a3 0)) (k2 a3 reftgen$n$0 a1 a3))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 true)) (k0 a1 reftgen$n$0) (>= a1 0) (= (mkadt0$0 (> a1 0)) (mkadt0$0 true)) (k1 a3 reftgen$n$0 a1) (>= a3 0) (k2 a4 reftgen$n$0 a1 a3) (not (= a4 (- reftgen$n$0 2)))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a3 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 true)) (k0 a1 reftgen$n$0) (>= a1 0) (= (mkadt0$0 (> a1 0)) (mkadt0$0 true)) (k1 a3 reftgen$n$0 a1) (>= a3 0) (not (= true (> reftgen$n$0 1)))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(a5 Adt1)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 true)) (k0 a1 reftgen$n$0) (>= a1 0) (= (mkadt0$0 (> a1 0)) (mkadt0$0 false)) (not (= false (> reftgen$n$0 1)))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(a6 Adt1)) (=> (and (>= reftgen$n$0 0) (= (mkadt0$0 (> reftgen$n$0 0)) (mkadt0$0 false)) (not (= false (> reftgen$n$0 1)))) false)))

(check-sat)
