(set-logic HORN)

;; Tag 0: Ret at 77:5: 77:14 (ESpan { span: tests/pos/surface/opt_blowup.rs:64:36: 64:41 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (< reftgen$n$0 a0) (< a0 a1) (< a1 a2)) (k0 a2 reftgen$n$0 a0 a1 a2))))
(assert (forall ((reftgen$n$0 Int)(a0 Int)(_$ Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)) (=> (and (< reftgen$n$0 a0) (< a0 a1) (< a1 a2) (k0 a3 reftgen$n$0 a0 a1 a2) (not (< reftgen$n$0 a3))) false)))

(check-sat)
