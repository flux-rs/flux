(set-logic HORN)

;; Tag 0: Call at 34:9: 34:23 (ESpan { span: tests/with_deps/pos/surface/for_range00.rs:6:25: 6:29 (#0), base: None })
;; Tag 1: Call at 35:9: 35:22 (ESpan { span: tests/with_deps/pos/surface/for_range00.rs:6:25: 6:29 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 1)(Adt1 0)) ((par (Par0) ((mkadt0$0 (fld0$0 Par0) (fld0$1 Par0))))((mkadt1$0 (fld1$0 Bool)))))
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (= reftgen$n$0 99) (k0 0 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (= reftgen$n$0 99) (k1 reftgen$n$0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Int))(_$ Int)(a1 (Adt0 Int))(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= reftgen$n$0 99) (k0 (fld0$0 a0) (fld0$1 a0) reftgen$n$0) (k1 (fld0$1 a0) reftgen$n$0) (=> (< (fld0$0 a0) (fld0$1 a0)) (= (fld0$0 a1) (+ (fld0$0 a0) 1))) (=> (not (< (fld0$0 a0) (fld0$1 a0))) (= (fld0$0 a1) (fld0$0 a0))) (= (fld0$1 a1) (fld0$1 a0)) (= (mkadt1$0 (< (fld0$0 a0) (fld0$1 a0))) (mkadt1$0 true)) (= a2 (fld0$0 a0)) (not (= (<= 0 a2) true))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Int))(_$ Int)(a1 (Adt0 Int))(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= reftgen$n$0 99) (k0 (fld0$0 a0) (fld0$1 a0) reftgen$n$0) (k1 (fld0$1 a0) reftgen$n$0) (=> (< (fld0$0 a0) (fld0$1 a0)) (= (fld0$0 a1) (+ (fld0$0 a0) 1))) (=> (not (< (fld0$0 a0) (fld0$1 a0))) (= (fld0$0 a1) (fld0$0 a0))) (= (fld0$1 a1) (fld0$1 a0)) (= (mkadt1$0 (< (fld0$0 a0) (fld0$1 a0))) (mkadt1$0 true)) (= a2 (fld0$0 a0)) (not (= (< a2 reftgen$n$0) true))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Int))(_$ Int)(a1 (Adt0 Int))(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= reftgen$n$0 99) (k0 (fld0$0 a0) (fld0$1 a0) reftgen$n$0) (k1 (fld0$1 a0) reftgen$n$0) (=> (< (fld0$0 a0) (fld0$1 a0)) (= (fld0$0 a1) (+ (fld0$0 a0) 1))) (=> (not (< (fld0$0 a0) (fld0$1 a0))) (= (fld0$0 a1) (fld0$0 a0))) (= (fld0$1 a1) (fld0$1 a0)) (= (mkadt1$0 (< (fld0$0 a0) (fld0$1 a0))) (mkadt1$0 true)) (= a2 (fld0$0 a0))) (k0 (fld0$0 a1) (fld0$1 a1) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 (Adt0 Int))(_$ Int)(a1 (Adt0 Int))(_$ Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (= reftgen$n$0 99) (k0 (fld0$0 a0) (fld0$1 a0) reftgen$n$0) (k1 (fld0$1 a0) reftgen$n$0) (=> (< (fld0$0 a0) (fld0$1 a0)) (= (fld0$0 a1) (+ (fld0$0 a0) 1))) (=> (not (< (fld0$0 a0) (fld0$1 a0))) (= (fld0$0 a1) (fld0$0 a0))) (= (fld0$1 a1) (fld0$1 a0)) (= (mkadt1$0 (< (fld0$0 a0) (fld0$1 a0))) (mkadt1$0 true)) (= a2 (fld0$0 a0))) (k1 (fld0$1 a1) reftgen$n$0))))

(check-sat)
