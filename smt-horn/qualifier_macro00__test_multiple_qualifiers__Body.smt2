(set-logic HORN)

;; Tag 0: Ret at 65:5: 65:8 (ESpan { span: tests/with_deps/pos/surface/qualifier_macro00.rs:54:31: 54:32 (#0), base: None })
;; Tag 1: Call at 61:9: 61:29 (ESpan { span: lib/flux-rs/src/lib.rs:9:15: 9:19 (#0), base: None })
;; Tag 2: Underflow at 62:9: 62:15

(declare-type-var T0)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int Int) Bool)
(declare-fun k1 (Int Int) Bool)

(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k0 reftgen$n$0 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)) (=> (>= reftgen$n$0 0) (k1 0 reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (not (> a0 0)) (not (= a1 reftgen$n$0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (= (= (+ a1 a0) reftgen$n$0) true))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0) (not (>= (- a0 1) 0))) false)))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0)) (k0 (- a0 1) (+ a1 1) reftgen$n$0))))
(assert (forall ((reftgen$n$0 Int)(_$ Int)(a0 Int)(a1 Int)(_$ Int)(_$ Int)) (=> (and (>= reftgen$n$0 0) (k0 a0 a1 reftgen$n$0) (k1 a1 reftgen$n$0) (> a0 0)) (k1 (+ a1 1) reftgen$n$0))))

(check-sat)
