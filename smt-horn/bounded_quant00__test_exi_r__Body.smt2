(set-logic HORN)

;; Tag 0: Ret at 52:35: 52:41 (ESpan { span: tests/pos/surface/bounded_quant00.rs:50:31: 50:42 (#0), base: None })
;; Tag 1: Ret at 52:5: 52:41 (ESpan { span: tests/pos/surface/bounded_quant00.rs:50:31: 50:42 (#0), base: None })

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (not (= reftgen$n$0 0)) (not (= reftgen$n$0 1)) (not (= reftgen$n$0 2)) (not (= (= reftgen$n$0 3) (or (or (or (= 0 reftgen$n$0) (= 1 reftgen$n$0)) (= 2 reftgen$n$0)) (= 3 reftgen$n$0))))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (not (= reftgen$n$0 0)) (not (= reftgen$n$0 1)) (not (not (= reftgen$n$0 2)))) (k0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(_$ Int)) (=> (and (not (= reftgen$n$0 0)) (not (not (= reftgen$n$0 1)))) (k0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (not (not (= reftgen$n$0 0))) (k0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (and (k0 reftgen$n$0) (not (= true (or (or (or (= 0 reftgen$n$0) (= 1 reftgen$n$0)) (= 2 reftgen$n$0)) (= 3 reftgen$n$0))))) false)))

(check-sat)
