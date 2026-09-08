(set-logic HORN)

;; Tag 0: Ret at 29:22: 29:31 (ESpan { span: tests/with_deps/pos/surface/promotion01.rs:27:30: 27:35 (#0), base: None })

(declare-type-var T0)
(declare-datatypes ((Adt0 0)) (((mkadt0$0) (mkadt0$1))))
(declare-fun gt (T0 T0) Bool)
(declare-fun ge (T0 T0) Bool)
(declare-fun lt (T0 T0) Bool)
(declare-fun le (T0 T0) Bool)
;; orig: $k0
(declare-fun k0 (Int) Bool)
;; orig: $k1
(declare-fun k1 (Adt0) Bool)
;; orig: $k2
(declare-fun k2 (Int) Bool)
;; orig: $k3
(declare-fun k3 (Adt0) Bool)

(assert (forall ((a0 Int)) (=> (= a0 0) (k0 a0))))
(assert (=> true (k1 mkadt0$1)))
(assert (forall ((a1 Int)) (=> (= a1 0) (k2 a1))))
(assert (=> true (k3 mkadt0$0)))
(assert (forall ((a2 Int)(_$ Int)(a3 Adt0)(_$ Int)(a4 Int)(_$ Int)(a5 Adt0)(_$ Int)) (=> (and (= a2 0) (k2 a2) (k3 a3) (= a4 0) (k0 a4) (k1 a5) (not (= (= a3 a5) false))) false)))

(check-sat)
