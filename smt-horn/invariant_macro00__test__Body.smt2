(set-logic HORN)

;; Tag 0: Ret at 27:5: 27:8 (ESpan { span: tests/with_deps/pos/surface/invariant_macro00.rs:18:31: 18:32 (#0), base: None })
;; Tag 1: Underflow at 23:50: 23:55
;; Tag 2: Underflow at 23:66: 23:73
;; Tag 3: Call at 50:9: 50:30 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 4: Underflow at 24:9: 24:15

(declare-type-var T0)
(declare-const gt (Array T0 (Array T0 Bool)))
(declare-const ge (Array T0 (Array T0 Bool)))
(declare-const lt (Array T0 (Array T0 Bool)))
(declare-const le (Array T0 (Array T0 Bool)))
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)
(declare-fun k2 (Int Int Int) Bool)
(declare-fun k3 (Bool Int Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k0 reftgen$n$0 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k1 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (not (> a0 0)) (not (= a1 reftgen$n$0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (= (+ a1 a0) reftgen$n$0))) (k2 reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (not (= (+ a1 a0) reftgen$n$0))) (not (>= (- 99 99) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (not (= (+ a1 a0) reftgen$n$0))) (not (>= a0 (- 99 99)))) (k2 reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (not (= (+ a1 a0) reftgen$n$0))) (>= a0 (- 99 99)) (not (>= (- 66 66) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (not (= (+ a1 a0) reftgen$n$0))) (>= a0 (- 99 99))) (k3 (>= a1 (- 66 66)) reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (k2 reftgen$n$0 a0 a1)) (k3 false reftgen$n$0 a0 a1))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (k3 a2 reftgen$n$0 a0 a1) (not (= a2 true))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (k3 a2 reftgen$n$0 a0 a1) (not (>= (- a0 1) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (k3 a2 reftgen$n$0 a0 a1)) (k0 (- a0 1) (+ a1 1) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)(a2 Bool)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (k3 a2 reftgen$n$0 a0 a1)) (k1 (+ a1 1) reftgen$n$0))))

(check-sat)
