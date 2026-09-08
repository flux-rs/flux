(set-logic HORN)

;; Tag 0: Ret at 27:5: 27:12 (ESpan { span: tests/pos/surface/dummy_join00.rs:16:36: 16:42 (#0), base: None })
;; Tag 1: Ret at 27:5: 27:12 (ESpan { span: tests/pos/surface/dummy_join00.rs:16:46: 16:52 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int) Bool)

(assert (forall ((a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (not (= a0 0)) (not (= a0 1)) (not (= a0 2))) (k0 4 a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (not (= a0 0)) (not (= a0 1)) (not (not (= a0 2)))) (k0 3 a0))))
(assert (forall ((a0 Int)(_$ Int)(_$ Int)) (=> (and (not (= a0 0)) (not (not (= a0 1)))) (k0 2 a0))))
(assert (forall ((a0 Int)(_$ Int)) (=> (not (not (= a0 0))) (k0 1 a0))))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (and (k0 a1 a0) (not (<= 2 (+ a1 1)))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)) (=> (and (k0 a1 a0) (not (<= (+ a1 1) 5))) false)))

(check-sat)
