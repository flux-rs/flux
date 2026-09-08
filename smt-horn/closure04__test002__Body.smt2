(set-logic HORN)

;; Tag 0: Predicate at 18:5: 18:13 (ESpan { span: tests/pos/surface/closure04.rs:13:59: 13:65 (#0), base: None })
;; Tag 1: Predicate at 18:5: 18:13 (ESpan { span: tests/pos/surface/closure04.rs:13:59: 13:65 (#0), base: None })
;; Tag 2: NoPanic(DefId(2:4245 ~ core[9471]::ops::function::Fn::call), MightPanic(NotInCallGraph)) at 18:5: 18:13
;; Tag 3: Ret at 19:1: 19:2 (ESpan { span: tests/pos/surface/closure04.rs:13:35: 13:39 (#0), base: None })

(declare-type-var T0)
(declare-const c0 Bool)
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
(declare-fun k0 (Int Int) Bool)
(declare-fun k1 (Int Int) Bool)
(declare-fun k2 (Int Int) Bool)

(assert (forall ((a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)) (=> (and (k0 a1 a0) (k1 a2 a0) (not (<= 0 a2))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)) (=> (and (k0 a1 a0) (k1 a2 a0) (k0 a3 a0) (k1 a4 a0) (not (<= 0 a4))) false)))
(assert (forall ((a0 Int)(a1 Int)(_$ Int)(a2 Int)(_$ Int)(a3 Int)(_$ Int)(a4 Int)(_$ Int)(a5 Int)(_$ Int)) (=> (and (k0 a1 a0) (k1 a2 a0) (k0 a3 a0) (k1 a4 a0) (<= 0 a5)) (k2 a5 a0))))
(assert (forall ((a0 Int)) (=> (not (=> false (or c0 false))) false)))
(assert (forall ((a0 Int)) (=> true (k0 a0 a0))))
(assert (forall ((a0 Int)) (=> true (k1 99 a0))))
(assert (forall ((a0 Int)(a6 Int)(_$ Int)) (=> (and (k2 a6 a0) (not (<= 0 a6))) false)))

(check-sat)
